(* ========================================================================= *)
(* pc_p2a_defs: definitions of the P2A layer (MT Ch 6-8).  Space-time views  *)
(* V = (TM,AT,G); regions and smooth parts; L-length, piecewise C^1 and      *)
(* admissible curves, junk-free minimizers; the L-geodesic system in         *)
(* s = sqrt tau; L-geodesics, Lexp, Jacobian, reduced-volume integrand,      *)
(* minimizer sets; chart-level L-functional.  Then the statement constants   *)
(* of the layer and the lemmas proved here.                                  *)
(* ========================================================================= *)

needs "src/pc_p3_route.ml";;
needs "src/pc_geo_local.ml";;
needs "src/pc_lrg_evol.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D0. Dimension-generic views (local form): copies, for real^N, of the     *)
(* view projections rfs_vtop, rfs_vatlas, rfs_vmetric, of rfs_persists and  *)
(* rfs_flow_view (pc_rfs_geom) and of rfs_flow_upto (pc_p3_defs), with the  *)
(* same texts; at N = 3 they agree with the 3-dimensional notions           *)
(* (P2A_VIEW_PROJ_3, P2A_PERSISTS_3, P2A_FLOW_VIEW_3, P2A_FLOW_UPTO_3).     *)
(* All view-level notions below are generic in N, for the 2-d versions      *)
(* needed for MT Cor 9.50.                                                  *)
(* ------------------------------------------------------------------------- *)

let p2a_vtop = new_definition
 `p2a_vtop (TM:real->A topology,AT:real->((A->bool)#(A->real^N))->bool,
            G:real->A->real^N^N) = TM`;;

let p2a_vatlas = new_definition
 `p2a_vatlas (TM:real->A topology,AT:real->((A->bool)#(A->real^N))->bool,
              G:real->A->real^N^N) = AT`;;

let p2a_vmetric = new_definition
 `p2a_vmetric (TM:real->A topology,AT:real->((A->bool)#(A->real^N))->bool,
               G:real->A->real^N^N) = G`;;

let p2a_persists = new_definition
 `p2a_persists (TM:real->A topology,AT:real->((A->bool)#(A->real^N))->bool,
                G:real->A->real^N^N) (W:A->bool) (a:real) (b:real) <=>
    !s. a < s /\ s <= b
        ==> smooth_manifold_atlas (TM s) (AT s) /\ open_in (TM s) W`;;

let p2a_flow_view = new_definition
 `p2a_flow_view (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                (J:real->bool) (g:real->A->real^N^N) =
    (\t. if t IN J then top else discrete_topology {}),
    (\t:real. atlas),g`;;

let p2a_flow_upto = new_definition
 `p2a_flow_upto (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                (a:real) (b:real) (g:real->A->real^N^N) <=>
    ricci_flow_on (top,atlas) a b g /\ riemannian_metric atlas (g b) /\
    !c. c IN atlas
        ==> ?e Fx. &0 < e /\
                   smooth_map_on
                     (interval(lift a,lift(b + e)) PCROSS IMAGE (SND c) (FST c)) Fx /\
                   !t y. a < t /\ t <= b /\ y IN IMAGE (SND c) (FST c)
                         ==> Fx(pastecart (lift t) y) =
                             (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c (g t) y)`;;

(* ------------------------------------------------------------------------- *)
(* D1. Regions (space-time charts of the smooth part).  On W over (a,b] the  *)
(* slices are open sets with smooth atlases (p2a_persists), the identity is  *)
(* a diffeomorphism of W between the slice atlas at s and the atlas at b,   *)
(* and the metric family moved to the atlas at b (the text of               *)
(* p3_region_flow) is a Ricci flow on W over (a,b], smooth up to b.         *)
(* ------------------------------------------------------------------------- *)

let p2a_rmetric = new_definition
 `p2a_rmetric (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) (W:A->bool) (b:real) (s:real) =
    restrict_metric (p2a_vatlas V b) W
      (\x. if s = b then p2a_vmetric V b x
           else mfd_pullback_metric (p2a_vatlas V b) (p2a_vatlas V s) (\y:A. y)
                                    (p2a_vmetric V s) x)`;;

let p2a_region = new_definition
 `p2a_region (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) (W:A->bool) (a:real) (b:real) <=>
    p2a_persists V W a b /\
    (!s. a < s /\ s <= b
         ==> mfd_diffeo (p2a_vtop V s) (p2a_vatlas V s) W
                        (p2a_vtop V b) (p2a_vatlas V b) W (\y:A. y) (\y. y)) /\
    p2a_flow_upto (subtopology (p2a_vtop V b) W,restrict_atlas (p2a_vatlas V b) W)
                  a b (p2a_rmetric V W b)`;;

(* Smooth points (two-sided regions; MT: interior points of space-time) and *)
(* backward-smooth points (a region ending at t; the base point of the       *)
(* L-geometry needs only this).                                              *)

let p2a_smooth = new_definition
 `p2a_smooth (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) (y:A) (t:real) <=>
    ?W a b. y IN W /\ a < t /\ t < b /\ p2a_region V W a b`;;

let p2a_bsmooth = new_definition
 `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) (y:A) (t:real) <=>
    ?W a. y IN W /\ a < t /\ p2a_region V W a t`;;

(* Smooth view settings: nonempty slices are Hausdorff smooth manifolds     *)
(* with Riemannian metrics (true for rfs_view hs and rfs_flow_view; empty   *)
(* slices are exempt, as in p2c_regular_view).                              *)

let p2a_svs = new_definition
 `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
             (real->A->real^N^N)) <=>
    !t. hausdorff_space (p2a_vtop V t) /\
        (~(topspace(p2a_vtop V t) = {})
         ==> smooth_manifold_atlas (p2a_vtop V t) (p2a_vatlas V t) /\
             riemannian_metric (p2a_vatlas V t) (p2a_vmetric V t))`;;

(* Compact subsets of the smooth part (view form of p3_st_compact, with    *)
(* regions instead of persisting sets): finitely many compact boxes.        *)

let p2a_cbox = new_definition
 `p2a_cbox (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (K:real->A->bool) <=>
    ?n W C a b eta.
      &0 < eta /\
      (!j:num. j < n
           ==> a j <= b j /\ (C j:A->bool) SUBSET W j /\
               p2a_region V (W j) (a j - eta) (b j) /\
               !s. a j <= s /\ s <= b j ==> compact_in (p2a_vtop V s) (C j)) /\
      (!t y. y IN K t ==> ?j. j < n /\ a j <= t /\ t <= b j /\ y IN C j)`;;

(* ------------------------------------------------------------------------- *)
(* D2. Curves parametrized by backward time from tt and their L-length (the  *)
(* text of p3_defs D6 with the view components; P2A_L_LENGTH_VIEW).          *)
(* ------------------------------------------------------------------------- *)

let p2a_L_integrand = new_definition
 `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                     (real->A->real^N^N)) (tt:real) (gamma:real->A) (b:real) (tau:real) =
    sqrt tau *
    (mfd_scalar (p2a_vatlas V (tt - tau)) (p2a_vmetric V (tt - tau)) (gamma tau) +
     mfd_speed (p2a_vatlas V (tt - tau)) (p2a_vmetric V (tt - tau))
               gamma (&0) b tau pow 2)`;;

let p2a_L_length = new_definition
 `p2a_L_length (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) (tt:real) (gamma:real->A) (b:real) =
    real_integral (real_interval[&0,b]) (p2a_L_integrand V tt gamma b)`;;

(* Piecewise C^1 on (a,b] with corner set P: at every time C^1 from each    *)
(* side in every chart of the slice atlas (only times sharing that atlas),  *)
(* two-sided off P.  At an event time of a history the two sides lie in     *)
(* different stages, so corners at event times are always allowed (as in    *)
(* rfs_st_curve); P lists the other corners (broken L-geodesics).           *)

let p2a_pc1 = new_definition
 `p2a_pc1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
             (real->A->real^N^N)) (tt:real) (gamma:real->A) (a:real) (b:real)
          (P:real->bool) <=>
    FINITE P /\
    !s0 c. a < s0 /\ s0 <= b /\ c IN p2a_vatlas V (tt - s0) /\ gamma s0 IN FST c
           ==> ?d. &0 < d /\
                   continuously_differentiable 1
                     {s | s0 - d <= drop s /\ drop s <= s0 /\ a < drop s /\
                          p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                          gamma(drop s) IN FST c}
                     (\s. SND c (gamma(drop s))) /\
                   continuously_differentiable 1
                     {s | s0 <= drop s /\ drop s <= s0 + d /\ drop s <= b /\
                          p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                          gamma(drop s) IN FST c}
                     (\s. SND c (gamma(drop s))) /\
                   (~(s0 IN P)
                    ==> continuously_differentiable 1
                          {s | s0 - d <= drop s /\ drop s <= s0 + d /\
                               a < drop s /\ drop s <= b /\
                               p2a_vatlas V (tt - drop s) = p2a_vatlas V (tt - s0) /\
                               gamma(drop s) IN FST c}
                          (\s. SND c (gamma(drop s))))`;;

(* Admissible curves from x on [0,b] (MT Def 6.1, with the path class fixed: *)
(* corners allowed, singular at tau = 0): in the slices, continuous in the   *)
(* slice topologies (clause 2 of rfs_st_curve), piecewise C^1, smooth points *)
(* for tau > 0, integrable L-integrand.                                      *)

let p2a_adm = new_definition
 `p2a_adm (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
             (real->A->real^N^N)) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    &0 < b /\ gamma(&0) = x /\
    (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN topspace(p2a_vtop V (tt - tau))) /\
    (!tau0 O. &0 <= tau0 /\ tau0 <= b /\ open_in (p2a_vtop V (tt - tau0)) O /\
              gamma tau0 IN O
              ==> ?d. &0 < d /\
                      !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau0) < d
                            ==> gamma tau IN O) /\
    (?P. p2a_pc1 V tt gamma (&0) b P) /\
    (!tau. &0 < tau /\ tau <= b ==> p2a_smooth V (gamma tau) (tt - tau)) /\
    p2a_L_integrand V tt gamma b real_integrable_on real_interval[&0,b]`;;

(* Minimizers, junk-free (no infimum): no admissible competitor with the    *)
(* same endpoint is shorter.  Lx and lx as in p3_defs; when a minimizer     *)
(* exists Lx is its length (P2A_MIN_LX).                                     *)

let p2a_min = new_definition
 `p2a_min (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
             (real->A->real^N^N)) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    p2a_adm V tt x b gamma /\
    !gamma'. p2a_adm V tt x b gamma' /\ gamma' b = gamma b
             ==> p2a_L_length V tt gamma b <= p2a_L_length V tt gamma' b`;;

let p2a_Lx = new_definition
 `p2a_Lx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
            (real->A->real^N^N)) (tt:real) (x:A) (b:real) (q:A) =
    inf {p2a_L_length V tt gamma b | gamma | p2a_adm V tt x b gamma /\ gamma b = q}`;;

let p2a_lx = new_definition
 `p2a_lx (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
            (real->A->real^N^N)) (tt:real) (x:A) (b:real) (q:A) =
    p2a_Lx V tt x b q / (&2 * sqrt b)`;;

(* ------------------------------------------------------------------------- *)
(* D3. The L-geodesic equation in s = sqrt tau (MT eq. (6.5), regular at    *)
(* s = 0): for a family Gt of local metrics on an open set of real^N       *)
(* (the chart level is dimension-generic: 2-d versions for MT Cor 9.50),    *)
(*    A' = -Gamma(A,A) + 2 s^2 grad R - 4 s Ric(A),   A = d gamma / ds,     *)
(* coefficients at time tt - s^2; the L-Lagrangian A.GA/2 + 2 s^2 R.        *)
(* ------------------------------------------------------------------------- *)

let p2a_lgradR = new_definition
 `p2a_lgradR (G:real^N->real^N^N) (y:real^N) =
    matrix_inv(G y) **
    ((lambda k. drop(frechet_derivative (\z. lift(lscalar G z)) (at y) (basis k))):real^N)`;;

let p2a_lricop = new_definition
 `p2a_lricop (G:real^N->real^N^N) (y:real^N) (v:real^N) =
    matrix_inv(G y) ** ((lambda k. lricci G y v (basis k)):real^N)`;;

let p2a_lacc = new_definition
 `p2a_lacc (Gt:real->real^N->real^N^N) (tt:real) (s:real) (y:real^N) (A:real^N) =
    --(christoffel (Gt(tt - s pow 2)) y A A) +
    (&2 * s pow 2) % p2a_lgradR (Gt(tt - s pow 2)) y -
    (&4 * s) % p2a_lricop (Gt(tt - s pow 2)) y A`;;

let p2a_llag = new_definition
 `p2a_llag (Gt:real->real^N->real^N^N) (tt:real) (s:real) (y:real^N) (A:real^N) =
    inv(&2) * (A dot (Gt(tt - s pow 2) y ** A)) +
    &2 * s pow 2 * lscalar (Gt(tt - s pow 2)) y`;;

(* The field of the first-order system in (y,A), for the ODE package.      *)

let p2a_lfield = new_definition
 `p2a_lfield (Gt:real->real^N->real^N^N) (tt:real)
             (z:real^(1,(N,N)finite_sum)finite_sum) =
    pastecart (sndcart(sndcart z))
              (p2a_lacc Gt tt (drop(fstcart z)) (fstcart(sndcart z))
                        (sndcart(sndcart z)))`;;

(* The local metric family of a region chart c (in the atlas at b).        *)

let p2a_rlocal = new_definition
 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) (W:A->bool) (b:real)
             (c:(A->bool)#(A->real^N)) (t:real) =
    metric_local (restrict_atlas (p2a_vatlas V b) W) c (p2a_rmetric V W b t)`;;

(* L-geodesics on [0,b] (MT Def 6.7): in the slices, smooth points for      *)
(* tau > 0, and near every s0 in [0, sqrt b] the chart curve                 *)
(* s |-> c(gamma(s^2)) of some region chart solves the system (6.5).        *)

let p2a_Lgeod = new_definition
 `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
               (real->A->real^N^N)) (tt:real) (gamma:real->A) (b:real) <=>
    &0 < b /\
    (!tau. &0 <= tau /\ tau <= b ==> gamma tau IN topspace(p2a_vtop V (tt - tau))) /\
    (!tau. &0 < tau /\ tau <= b ==> p2a_smooth V (gamma tau) (tt - tau)) /\
    !s0. &0 <= s0 /\ s0 pow 2 <= b
         ==> ?W a' b' c d (A:real^1->real^N).
               p2a_region V W a' b' /\
               c IN restrict_atlas (p2a_vatlas V b') W /\ &0 < d /\
               (!s. &0 <= s /\ s pow 2 <= b /\ abs(s - s0) < d
                    ==> gamma(s pow 2) IN FST c /\
                        a' < tt - s pow 2 /\ tt - s pow 2 <= b') /\
               (!u. &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < d
                    ==> ((\v. SND c (gamma(drop v pow 2))) has_vector_derivative A u)
                          (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
                        (A has_vector_derivative
                           p2a_lacc (p2a_rlocal V W b' c) tt (drop u)
                                    (SND c (gamma(drop u pow 2))) (A u))
                          (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}))`;;

(* L-geodesics from x with initial vector Z (MT Lemma 6.8: the limit of     *)
(* sqrt(tau) X(tau) is Z, i.e. d/ds at s = 0 is 2 Z), in the preferred      *)
(* chart of the slice atlas at tt at x.                                      *)

let p2a_Lgeod_from = new_definition
 `p2a_Lgeod_from (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)) (tt:real) (x:A) (Z:real^N) (b:real)
                 (gamma:real->A) <=>
    p2a_Lgeod V tt gamma b /\ gamma(&0) = x /\
    ((\v. SND(chart_at (p2a_vatlas V tt) x) (gamma(drop v pow 2)))
     has_vector_derivative (&2 % Z))
    (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b})`;;

(* The domain D_x at tau = b, the L-geodesic gamma_Z, Lexp^b, the length    *)
(* L~(Z,b) and the reduced length l~(Z,b) (MT Defs 6.17, 6.52).             *)

let p2a_Ldom = new_definition
 `p2a_Ldom (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) =
    {Z:real^N | ?gamma. p2a_Lgeod_from V tt x Z b gamma}`;;

let p2a_Lgeo = new_definition
 `p2a_Lgeo (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (Z:real^N) (b:real) =
    @gamma:real->A. p2a_Lgeod_from V tt x Z b gamma`;;

let p2a_Lexp = new_definition
 `p2a_Lexp (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) (Z:real^N) =
    p2a_Lgeo V tt x Z b b`;;

let p2a_Ltil = new_definition
 `p2a_Ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) (Z:real^N) =
    p2a_L_length V tt (p2a_Lgeo V tt x Z b) b`;;

let p2a_ltil = new_definition
 `p2a_ltil (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) (Z:real^N) =
    p2a_Ltil V tt x b Z / (&2 * sqrt b)`;;

(* The Jacobian J(Z,b) of Lexp^b with respect to the measures dvol for     *)
(* g(tt - b) and dZ for g(tt) (MT Lemma 6.71), the reduced-volume          *)
(* integrand b^(-n/2) exp(-l~) J with n = dimindex(:N) (MT Def 6.70), the  *)
(* squared norm of Z for g(tt) at x, and the reference measure on Z-space. *)

let p2a_J = new_definition
 `p2a_J (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
           (real->A->real^N^N)) (tt:real) (x:A) (b:real) (Z:real^N) =
    abs(det(matrix(frechet_derivative
          (\W. SND(chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
                  (p2a_Lexp V tt x b W)) (at Z)))) *
    mfd_density (p2a_vatlas V (tt - b))
                (chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
                (p2a_vmetric V (tt - b))
                (SND(chart_at (p2a_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
                    (p2a_Lexp V tt x b Z)) /
    mfd_density (p2a_vatlas V tt) (chart_at (p2a_vatlas V tt) x) (p2a_vmetric V tt)
                (SND(chart_at (p2a_vatlas V tt) x) x)`;;

let p2a_rvi = new_definition
 `p2a_rvi (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
             (real->A->real^N^N)) (tt:real) (x:A) (b:real) (Z:real^N) =
    exp(--(p2a_ltil V tt x b Z)) * p2a_J V tt x b Z / sqrt b pow dimindex(:N)`;;

let p2a_znorm2 = new_definition
 `p2a_znorm2 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                (real->A->real^N^N)) (tt:real) (x:A) (Z:real^N) =
    Z dot (p2a_vmetric V tt x ** Z)`;;

let p2a_zdens = new_definition
 `p2a_zdens (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
               (real->A->real^N^N)) (tt:real) (x:A) =
    mfd_density (p2a_vatlas V tt) (chart_at (p2a_vatlas V tt) x) (p2a_vmetric V tt)
                (SND(chart_at (p2a_vatlas V tt) x) x)`;;

(* The initial vectors of minimizers at tau = b (the set W~ of the route    *)
(* below; it replaces the injectivity set U~_x(b) of MT Def 6.25).           *)

let p2a_Smin = new_definition
 `p2a_Smin (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) =
    {Z | Z IN p2a_Ldom V tt x b /\ p2a_min V tt x b (p2a_Lgeo V tt x Z b)}`;;

(* ------------------------------------------------------------------------- *)
(* V1. Vocabulary.  Corner-free admissible curves (corners only where the   *)
(* slice atlas changes: for a history exactly rfs_L_adm, P2A_HIST_VIEW),    *)
(* open space-time sets and slice minimizers (view forms of p3_st_open and  *)
(* p3_Lmin_set), and the squared gradient of R in the preferred chart.      *)
(* ------------------------------------------------------------------------- *)

let p2a_adm1 = new_definition
 `p2a_adm1 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
              (real->A->real^N^N)) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    p2a_adm V tt x b gamma /\ p2a_pc1 V tt gamma (&0) b {}`;;

let p2a_st_open = new_definition
 `p2a_st_open (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) (U:real->A->bool) (a:real) (b:real) <=>
    (!t y. y IN U t ==> a <= t /\ t < b) /\
    !t y. y IN U t
          ==> ?W eta. &0 < eta /\ y IN W /\ p2a_persists V W (t - eta) (t + eta) /\
                      !s. t - eta < s /\ s < t + eta /\ a <= s /\ s < b ==> W SUBSET U s`;;

let p2a_Lmin_set = new_definition
 `p2a_Lmin_set (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                  (real->A->real^N^N)) (tt:real) (x:A) (U:real->A->bool) (t:real) =
    {y | y IN U t /\
         !z. z IN U t ==> p2a_Lx V tt x (tt - t) y <= p2a_Lx V tt x (tt - t) z}`;;

let p2a_vgradR2 = new_definition
 `p2a_vgradR2 (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) (t:real) (y:A) =
    lgrad2 (metric_local (p2a_vatlas V t) (chart_at (p2a_vatlas V t) y) (p2a_vmetric V t))
           (lscalar (metric_local (p2a_vatlas V t) (chart_at (p2a_vatlas V t) y)
                                  (p2a_vmetric V t)))
           (SND(chart_at (p2a_vatlas V t) y) y)`;;


(* Chart level (dimension-generic): smooth metric families, L-functional  *)
(* and energy in s.                                                          *)

let p2a_lsmooth = new_definition
 `p2a_lsmooth (U:real^N->bool) (ta:real) (tb:real) (Gt:real->real^N->real^N^N) <=>
    open U /\ ta < tb /\
    (!t. ta < t /\ t < tb ==> metric_field U (Gt t)) /\
    smooth_map_on (interval(lift ta,lift tb) PCROSS U)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (Gt (drop(fstcart z)) (sndcart z)))`;;
let p2a_cL = new_definition
 `p2a_cL (Gt:real->real^N->real^N^N) (tt:real) (sig:real^1->real^N) (s1:real) (s2:real) =
    real_integral (real_interval[s1,s2])
      (\s. p2a_llag Gt tt s (sig(lift s)) (vector_derivative sig (at (lift s))))`;;
let p2a_cE = new_definition
 `p2a_cE (Gt:real->real^N->real^N^N) (tt:real) (sig:real^1->real^N) (s1:real) (s2:real) =
    real_integral (real_interval[s1,s2])
      (\s. vector_derivative sig (at (lift s)) dot vector_derivative sig (at (lift s)))`;;

(* Views whose persisting sets have smooth transitions: the identity is a   *)
(* diffeomorphism of W between the slice atlases at s and at b.  True for  *)
(* histories (event diffeomorphisms of mfd_cut_cap) and for flow views      *)
(* (one atlas); p2a_region asks for it, p2c_regular_view does not.          *)

let p2a_smooth_trans = new_definition
 `p2a_smooth_trans (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                      (real->A->real^N^N)) <=>
    !W a b s. a < s /\ s <= b /\ p2a_persists V W a b
              ==> mfd_diffeo (p2a_vtop V s) (p2a_vatlas V s) W
                             (p2a_vtop V b) (p2a_vatlas V b) W (\y:A. y) (\y. y)`;;

(* ========================================================================= *)
(* The statement constants of the P2A layer: statements proved in other     *)
(* layers (R), leaf statements (L1-L13), the view-level cores of the three  *)
(* main theorems (C1-C3), the history bridge, the Dini statement and the    *)
(* route obligations (O3-O11).  Statements only.                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* R. Statements proved in other layers (exact terms).                       *)
(* P3_LEMMA_14_11_STATEMENT (Part 3) is used as it stands.                   *)
(* ------------------------------------------------------------------------- *)

(* P2A_REQ_SHI_SCALED_STATEMENT: Shi's interior estimate for nabla Rm in     *)
(* scale-invariant form (P2_THM_3_28 with l = 1, K = r^-2, tau = r^2,        *)
(* constant independent of r; MT Claim 8.5 rescales to r = 1).               *)

let P2A_REQ_SHI_SCALED_STATEMENT = new_definition
 `P2A_REQ_SHI_SCALED_STATEMENT (u:A->bool) <=>
    ?C. &0 < C /\
        !top atlas a b g x r.
          hausdorff_space top /\
          rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
          &0 < r /\ r pow 2 <= b - a /\ x IN topspace top /\
          compact_in top (top closure_of mfd_ball (top,atlas) (g b) x r) /\
          (!t y. a < t /\ t <= b /\ y IN mfd_ball (top,atlas) (g b) x r
                 ==> mfd_rm_norm atlas (g t) y <= inv(r pow 2))
          ==> !y. y IN mfd_ball (top,atlas) (g b) x (r / &2)
                  ==> lrm_deriv_norm2 1 (metric_local atlas (chart_at atlas y) (g b))
                                        (SND(chart_at atlas y) y) <= C * inv(r pow 6)`;;

(* P2A_REQ_RLOWER_STATEMENT: the scalar curvature of a Ricci flow on a       *)
(* closed manifold is bounded below by min(0, min R at the initial time)     *)
(* (maximum principle; makes every rfs_Lx an honest infimum).                *)

let P2A_REQ_RLOWER_STATEMENT = new_definition
 `P2A_REQ_RLOWER_STATEMENT (u:A->bool) <=>
    !top atlas a b g.
       hausdorff_space top /\ compact_space top /\
       ricci_flow_from (top,atlas:((A->bool)#(A->real^3))->bool) a b g
       ==> !t x. a <= t /\ t < b /\ x IN topspace top
                 ==> min (&0) (inf {mfd_scalar atlas (g a) y | y IN topspace top})
                     <= mfd_scalar atlas (g t) x`;;

(* P2A_REQ_AREA_STATEMENT (proved as MFD_AREA_FORMULA in pc_grg_area): the  *)
(* area formula for a continuous map F from a Lebesgue measurable set of    *)
(* real^3 into a manifold, differentiable in charts: the image has a volume *)
(* at most the integral of the Jacobian |det F'| times the density, with    *)
(* equality for injective F.                                                *)
(* Continuity keeps the chart composites meaningful (charts are total       *)
(* functions with junk values off their domains).                           *)

let P2A_REQ_AREA_STATEMENT = new_definition
 `P2A_REQ_AREA_STATEMENT (u:A->bool) <=>
    !top atlas g (Fm:real^3->A) Fm' S.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\
       lebesgue_measurable S /\ IMAGE Fm S SUBSET topspace top /\
       continuous_map (subtopology euclidean S,top) Fm /\
       (!Z. Z IN S
            ==> ((\W. SND(chart_at atlas (Fm Z)) (Fm W)) has_derivative Fm' Z)
                (at Z within S)) /\
       (\Z. lift(abs(det(matrix(Fm' Z))) *
                 mfd_density atlas (chart_at atlas (Fm Z)) g (SND(chart_at atlas (Fm Z)) (Fm Z))))
       integrable_on S
       ==> ?v. mfd_has_volume (top,atlas) g (IMAGE Fm S) v /\
               v <= drop(integral S
                      (\Z. lift(abs(det(matrix(Fm' Z))) *
                                mfd_density atlas (chart_at atlas (Fm Z)) g
                                            (SND(chart_at atlas (Fm Z)) (Fm Z))))) /\
               ((!Z Z'. Z IN S /\ Z' IN S /\ Fm Z = Fm Z' ==> Z = Z')
                ==> v = drop(integral S
                           (\Z. lift(abs(det(matrix(Fm' Z))) *
                                     mfd_density atlas (chart_at atlas (Fm Z)) g
                                                 (SND(chart_at atlas (Fm Z)) (Fm Z))))))`;;

(* P2A_REQ_VOLCMP_STATEMENT (MFD_HAS_VOLUME_COMPARE_QF): volume comparison   *)
(* under comparison of metrics.                                              *)

let P2A_REQ_VOLCMP_STATEMENT = new_definition
 `P2A_REQ_VOLCMP_STATEMENT (u:A->bool) <=>
    !top atlas g g' S v v' lam.
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ riemannian_metric atlas g' /\ &0 <= lam /\
       mfd_has_volume (top,atlas) g S v /\ mfd_has_volume (top,atlas) g' S v' /\
       (!y w. y IN S ==> w dot (g y ** w) <= lam * (w dot (g' y ** w)))
       ==> v <= lam * sqrt lam * v'`;;

(* ------------------------------------------------------------------------- *)
(* L. Leaf statements of the P2A layer (proved from the foundations, the    *)
(* statements R above and the ODE package pc_ode_vf).                       *)
(* ------------------------------------------------------------------------- *)

(* L1 (MT Lemmas 6.8, 6.18): the L-geodesic flow from a backward-smooth     *)
(* base point: uniqueness, restriction, local existence, open domains, Lexp *)
(* differentiable in charts, the integrand continuous.                      *)

let P2A_LGEOD_FLOW_STATEMENT = new_definition
 `P2A_LGEOD_FLOW_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x.
       p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt
       ==> (!Z b gamma gamma'.
               p2a_Lgeod_from V tt x Z b gamma /\ p2a_Lgeod_from V tt x Z b gamma'
               ==> !tau. &0 <= tau /\ tau <= b ==> gamma tau = gamma' tau) /\
           (!Z b b'. Z IN p2a_Ldom V tt x b /\ &0 < b' /\ b' <= b
                     ==> Z IN p2a_Ldom V tt x b' /\
                         !tau. &0 <= tau /\ tau <= b'
                               ==> p2a_Lgeo V tt x Z b' tau = p2a_Lgeo V tt x Z b tau) /\
           (!Z. ?b. &0 < b /\ Z IN p2a_Ldom V tt x b) /\
           (!b. open(p2a_Ldom V tt x b)) /\
           (!b Z. Z IN p2a_Ldom V tt x b
                  ==> (\W. SND(chart_at (rfs_vatlas V (tt - b)) (p2a_Lexp V tt x b Z))
                              (p2a_Lexp V tt x b W)) differentiable (at Z)) /\
           (!b. (\Z. lift(p2a_rvi V tt x b Z)) continuous_on p2a_Ldom V tt x b)`;;

(* L2 (MT Lemma 7.2 regularity, by local uniqueness; pc_p2a_bvp):           *)
(* minimizers are corner-free L-geodesics from x.                           *)

let P2A_MIN_LGEOD_STATEMENT = new_definition
 `P2A_MIN_LGEOD_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma.
       p2a_svs V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma
       ==> ?Z. Z IN p2a_Ldom V tt x b /\ p2a_pc1 V tt gamma (&0) b {} /\
               !tau. &0 <= tau /\ tau <= b ==> gamma tau = p2a_Lgeo V tt x Z b tau`;;

(* L3: restrictions of minimizers are minimizers.                            *)

let P2A_MIN_RESTRICT_STATEMENT = new_definition
 `P2A_MIN_RESTRICT_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b b' gamma.
       p2a_svs V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma /\ &0 < b' /\ b' <= b
       ==> p2a_min V tt x b' gamma`;;

(* L4 (MT Prop 6.30 first half, with the corner-cutting first variation;    *)
(* pc_p2a_bvp): Lexp at an earlier time is injective on the initial vectors *)
(* of minimizers (a minimizer with a corner would be shortened).            *)

let P2A_INJ_STATEMENT = new_definition
 `P2A_INJ_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b b1 Z Z'.
       p2a_svs V /\ p2a_bsmooth V x tt /\
       Z IN p2a_Smin V tt x b /\ Z' IN p2a_Smin V tt x b /\ &0 < b1 /\ b1 < b /\
       p2a_Lexp V tt x b1 Z = p2a_Lexp V tt x b1 Z'
       ==> Z = Z'`;;

(* L5 (MT Prop 6.81 with Props 6.30, 6.37, 6.43): along a minimizer the     *)
(* reduced-volume integrand is non-increasing in tau.                       *)

let P2A_RVI_MONO_STATEMENT = new_definition
 `P2A_RVI_MONO_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b Z b1 b2.
       p2a_svs V /\ p2a_bsmooth V x tt /\ Z IN p2a_Smin V tt x b /\
       &0 < b1 /\ b1 <= b2 /\ b2 <= b
       ==> p2a_rvi V tt x b2 Z <= p2a_rvi V tt x b1 Z`;;

(* L6 (MT Prop 6.78, Lemma 6.75): the integrand tends to 2^3 exp(-|Z|^2) as *)
(* tau -> 0.                                                                *)

let P2A_RVI_ASYMP_STATEMENT = new_definition
 `P2A_RVI_ASYMP_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x Z.
       p2a_svs V /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt
       ==> ((\b. p2a_rvi V tt x b Z) ---> &8 * exp(--(p2a_znorm2 V tt x Z)))
           (atreal (&0) within {b | &0 < b})`;;

(* L7 (pc_p2a_bvp): Lx is upper semicontinuous on slices (any curve to q is *)
(* modified near its end into curves to nearby points).                     *)

let P2A_LX_USC_STATEMENT = new_definition
 `P2A_LX_USC_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma e.
       p2a_svs V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\ &0 < e
       ==> ?O. open_in (rfs_vtop V (tt - b)) O /\ gamma b IN O /\
               !q. q IN O
                   ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = q /\
                                p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e`;;

(* L8 (MT Claims 8.5 and 8.8, the latter at tau1 = eps r^2): on a           *)
(* parabolic region with abs Rm <= r^-2, abs(grad R) <= C1 r^-3 on the      *)
(* half ball for the second half of the time interval, and the metrics at   *)
(* times s and tt (moved to the atlas at tt) are                            *)
(* exp(4 (tt - s) / r^2)-comparable.                                        *)

let P2A_PARABOLIC_STATEMENT = new_definition
 `P2A_PARABOLIC_STATEMENT (u:A->bool) <=>
    ?C1. &0 < C1 /\
         !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) tt x r.
            p2a_svs V /\ &0 < r /\ x IN topspace(rfs_vtop V tt) /\
            p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
            compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
            (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
                   ==> p3_vrm V s y <= inv(r pow 2))
            ==> (!s y. tt - r pow 2 / &2 <= s /\ s <= tt /\ y IN rfs_vball V tt x (r / &2)
                       ==> p2a_vgradR2 V s y <= C1 pow 2 * inv(r pow 6)) /\
                (!s y w. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
                         ==> w dot (p2a_rmetric V (rfs_vball V tt x r) tt s y ** w) <=
                             exp(&4 * (tt - s) / r pow 2) *
                             (w dot (p2a_rmetric V (rfs_vball V tt x r) tt tt y ** w)) /\
                             w dot (p2a_rmetric V (rfs_vball V tt x r) tt tt y ** w) <=
                             exp(&4 * (tt - s) / r pow 2) *
                             (w dot (p2a_rmetric V (rfs_vball V tt x r) tt s y ** w)))`;;

(* L9 (MT Claims 8.6-8.7, corrected: constant C(n) eps instead of 2): for   *)
(* eps small, L-geodesics from x with |Z| <= eps^-1/2 / 8 defined up to     *)
(* tau1 = eps r^2 stay in the half ball and have l~ >= -2 eps               *)
(* (n(n-1)/3 = 2).                                                          *)

let P2A_SMALLZ_STATEMENT = new_definition
 `P2A_SMALLZ_STATEMENT (u:A->bool) <=>
    !taub. &0 < taub
      ==> ?eps0. &0 < eps0 /\
            !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) tt x r eps Z.
               p2a_svs V /\ &0 < r /\ r pow 2 <= taub /\ x IN topspace(rfs_vtop V tt) /\
               p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
               compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
               (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
                      ==> p3_vrm V s y <= inv(r pow 2)) /\
               &0 < eps /\ eps <= eps0 /\
               Z IN p2a_Ldom V tt x (eps * r pow 2) /\
               &64 * eps * p2a_znorm2 V tt x Z <= &1
               ==> (!tau. &0 <= tau /\ tau <= eps * r pow 2
                          ==> p2a_Lgeo V tt x Z (eps * r pow 2) tau IN
                              rfs_vball V tt x (r / &2)) /\
                   --(&2 * eps) <= p2a_ltil V tt x (eps * r pow 2) Z`;;

(* L10 (MT Lemma 8.9, pure analysis): the Gaussian tail.                    *)

let P2A_GAUSS_TAIL_STATEMENT = new_definition
 `P2A_GAUSS_TAIL_STATEMENT <=>
    ?eps0. &0 < eps0 /\
      !eps. &0 < eps /\ eps <= eps0
            ==> (\Z:real^3. lift(&8 * exp(--(Z dot Z))))
                absolutely_integrable_on {Z | &1 <= &64 * eps * (Z dot Z)} /\
                drop(integral {Z | &1 <= &64 * eps * (Z dot Z)}
                       (\Z:real^3. lift(&8 * exp(--(Z dot Z))))) <= eps * sqrt eps`;;

(* L11 (pc_p2a_bvp, chart level): the local boundary value problem for      *)
(* short L-geodesics, with convexity of the L-functional.  For a local      *)
(* Ricci flow on an open U for times (ta,tb) (the flow equation is needed:  *)
(* (6.5) is the Euler-Lagrange equation of L only for Ricci flows, and for  *)
(* G(t) = (1 + t) mat 1 the solutions of (6.5) do not minimize),            *)
(* a compact Kc in U, an energy bound E and an s-range whose times lie in   *)
(* (ta,tb), there are delta, rho and a solution map sol: points at          *)
(* s-distance at most delta and chart distance at most rho are joined by a  *)
(* solution of (6.5), the unique minimizer of the L-functional among C^1    *)
(* chart curves in U of energy at most E, with L continuous in the data.    *)







let P2A_LOC_BVP_STATEMENT = new_definition
 `P2A_LOC_BVP_STATEMENT <=>
    !U ta tb (Gt:real->real^3->real^3^3) tt Kc E sa sb.
       p2a_lsmooth U ta tb Gt /\ lricci_flow U ta tb Gt /\
       compact Kc /\ Kc SUBSET U /\ &0 <= sa /\ sa < sb /\
       ta < tt - sb pow 2 /\ tt - sa pow 2 < tb /\ &0 < E
       ==> ?delta rho (sol:real->real->real^3->real^3->real^1->real^3).
             &0 < delta /\ &0 < rho /\
             (!s1 s2 y1 y2.
                sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                y1 IN Kc /\ norm(y2 - y1) <= rho
                ==> sol s1 s2 y1 y2 (lift s1) = y1 /\ sol s1 s2 y1 y2 (lift s2) = y2 /\
                    (!s. s1 <= s /\ s <= s2 ==> sol s1 s2 y1 y2 (lift s) IN U) /\
                    (!s. s1 <= s /\ s <= s2
                         ==> (sol s1 s2 y1 y2 has_vector_derivative
                              vector_derivative (sol s1 s2 y1 y2) (at (lift s)))
                             (at (lift s)) /\
                             ((\v. vector_derivative (sol s1 s2 y1 y2) (at v))
                              has_vector_derivative
                              p2a_lacc Gt tt s (sol s1 s2 y1 y2 (lift s))
                                       (vector_derivative (sol s1 s2 y1 y2) (at (lift s))))
                             (at (lift s))) /\
                    !sig'. sig'(lift s1) = y1 /\ sig'(lift s2) = y2 /\
                           (!s. s1 <= s /\ s <= s2 ==> sig'(lift s) IN U) /\
                           continuously_differentiable 1 (interval[lift s1,lift s2]) sig' /\
                           p2a_cE Gt tt sig' s1 s2 <= E
                           ==> p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 <= p2a_cL Gt tt sig' s1 s2 /\
                               (p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2 = p2a_cL Gt tt sig' s1 s2
                                ==> !s. s1 <= s /\ s <= s2
                                        ==> sig'(lift s) = sol s1 s2 y1 y2 (lift s))) /\
             (!s1 s2 y1 y2 s1n s2n y1n y2n.
                sa <= s1 /\ s1 < s2 /\ s2 <= sb /\ s2 - s1 <= delta /\
                y1 IN Kc /\ norm(y2 - y1) <= rho /\
                (!n:num. sa <= s1n n /\ s1n n < s2n n /\ s2n n <= sb /\
                         s2n n - s1n n <= delta /\ y1n n IN Kc /\
                         norm(y2n n - y1n n) <= rho) /\
                ((\n. lift(s1n n)) --> lift s1) sequentially /\
                ((\n. lift(s2n n)) --> lift s2) sequentially /\
                (y1n --> y1) sequentially /\ (y2n --> y2) sequentially
                ==> ((\n. lift(p2a_cL Gt tt (sol (s1n n) (s2n n) (y1n n) (y2n n))
                                     (s1n n) (s2n n)))
                     --> lift(p2a_cL Gt tt (sol s1 s2 y1 y2) s1 s2)) sequentially)`;;

(* L12 (pc_p2a_bvp): smoothing corners.  An admissible curve can be         *)
(* replaced by a corner-free one with the same end point, uniformly close,  *)
(* with L-length at most e larger (gives rfs_Lx = p2a_Lx for histories).    *)

let P2A_SMOOTHING_STATEMENT = new_definition
 `P2A_SMOOTHING_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma e.
       p2a_svs V /\ p2a_bsmooth V x tt /\ p2a_adm V tt x b gamma /\ &0 < e
       ==> ?gamma'. p2a_adm1 V tt x b gamma' /\ gamma' b = gamma b /\
                    p2a_L_length V tt gamma' b <= p2a_L_length V tt gamma b + e /\
                    !tau. &0 <= tau /\ tau <= b
                          ==> mfd_dist (rfs_vtop V (tt - tau),rfs_vatlas V (tt - tau))
                                       (rfs_vmetric V (tt - tau))
                                       (gamma' tau) (gamma tau) < e`;;

(* L13 (MT Prop 7.8 with Prop 6.31, Lemmas 6.47, 6.49; pc_p2a_bar), in the  *)
(* junk-free form the comparison argument uses: if a minimizer gamma to q   *)
(* is shorter than every admissible curve ending in an open set O around q  *)
(* (q is a local minimum point of lx in its slice), then for every e > 0    *)
(* and every slightly larger backward time b' there is a corner-free        *)
(* admissible curve to q at b' whose reduced length exceeds lx(q,b) by at   *)
(* most ((3/2 - lx(q,b))/b + e)(b' - b).                                    *)

let P2A_BARRIER_STATEMENT = new_definition
 `P2A_BARRIER_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     tt x b gamma O e.
       p2a_svs V /\ p2a_bsmooth V x tt /\ p2a_min V tt x b gamma /\ &0 < e /\
       open_in (rfs_vtop V (tt - b)) O /\ gamma b IN O /\
       (!g'. p2a_adm V tt x b g' /\ g' b IN O
             ==> p2a_L_length V tt gamma b <= p2a_L_length V tt g' b)
       ==> ?d. &0 < d /\
               !b'. b < b' /\ b' < b + d
                    ==> ?g'. p2a_adm1 V tt x b' g' /\ g' b' = gamma b /\
                             p2a_L_length V tt g' b' / (&2 * sqrt b') -
                             p2a_L_length V tt gamma b / (&2 * sqrt b) <=
                             ((&3 / &2 - p2a_L_length V tt gamma b / (&2 * sqrt b)) / b + e) *
                             (b' - b)`;;

(* ------------------------------------------------------------------------- *)
(* C1. MT Thm 8.1 for smooth view settings (generalized Ricci flows), in    *)
(* the form of P2_THM_8_1: half-open parabolic neighbourhood (as in MT Defs *)
(* 9.1 and 14.14), and instead of W~ in the injectivity set (MT (4)-(5)) an *)
(* open B of volume >= V0 every point of which is the end point of a        *)
(* minimizer of L <= 2 sqrt(tau0) l0.  No injectivity domain, Prop 6.56     *)
(* or Cor 6.67 is used.                                                     *)
(* ------------------------------------------------------------------------- *)

let P2A_THM_8_1_VIEW_STATEMENT = new_definition
 `P2A_THM_8_1_VIEW_STATEMENT (u:A->bool) <=>
    !taub l0 V0. &0 < taub /\ &0 < V0
      ==> ?kappa. &0 < kappa /\
            !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) x tt r tau0 B.
               p2a_svs V /\ &0 < tau0 /\ tau0 <= taub /\ &0 < r /\ r pow 2 <= tau0 /\
               x IN topspace(rfs_vtop V tt) /\
               p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
               compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
               (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
                      ==> p3_vrm V s y <= inv(r pow 2)) /\
               open_in (rfs_vtop V (tt - tau0)) B /\
               (?v. mfd_has_volume (rfs_vtop V (tt - tau0),rfs_vatlas V (tt - tau0))
                                   (rfs_vmetric V (tt - tau0)) B v /\ V0 <= v) /\
               (!q. q IN B
                    ==> ?gamma. p2a_min V tt x tau0 gamma /\ gamma tau0 = q /\
                                p2a_L_length V tt gamma tau0 <= &2 * sqrt tau0 * l0)
               ==> ?v. mfd_has_volume (rfs_vtop V tt,rfs_vatlas V tt) (rfs_vmetric V tt)
                                      (rfs_vball V tt x r) v /\
                       kappa * r pow 3 <= v`;;

(* ------------------------------------------------------------------------- *)
(* C2. MT Lemma 7.2 / Prop 16.21(1)-(2) in compact subsets of the smooth    *)
(* part (direct method by broken L-geodesics), corrected: the uniform limit *)
(* gamma is only continuous; what is claimed of it is that the L-distance  *)
(* of its end point is at most the liminf of the lengths (realized by      *)
(* corner-free competitors) and, for minimizing sequences with a fixed end, *)
(* that it is a corner-free minimizer.                                       *)
(* ------------------------------------------------------------------------- *)

(* Clause (c) also gives the end point gamma tau0 = q, as                 *)
(* P2_LEMMA_7_2_STATEMENT does.                                           *)
let P2A_LEMMA_7_2_VIEW_STATEMENT = new_definition
 `P2A_LEMMA_7_2_VIEW_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     x tt tau0 K gs Lb.
       p2a_svs V /\ &0 < tau0 /\ x IN topspace(rfs_vtop V tt) /\ p2a_bsmooth V x tt /\
       p2a_cbox V K /\
       (!n. p2a_adm V tt x tau0 (gs n) /\ p2a_L_length V tt (gs n) tau0 <= Lb /\
            !tau. &0 < tau /\ tau <= tau0 ==> gs n tau IN K (tt - tau))
       ==> ?sub gamma K'.
              p3_subseq sub /\ p2a_cbox V K' /\ gamma (&0) = x /\
              (!tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K' (tt - tau)) /\
              (!eta. &0 < eta
                     ==> (?gamma'. p2a_adm1 V tt x tau0 gamma' /\ gamma' tau0 = gamma tau0 /\
                                   (!tau. &0 < tau /\ tau <= tau0
                                          ==> gamma' tau IN K' (tt - tau)) /\
                                   ?N. !n. N <= n
                                       ==> p2a_L_length V tt gamma' tau0 <=
                                           p2a_L_length V tt (gs (sub n)) tau0 + eta) /\
                         (?N. !n. N <= n
                              ==> !tau. &0 <= tau /\ tau <= tau0
                                        ==> mfd_dist (rfs_vtop V (tt - tau),
                                                      rfs_vatlas V (tt - tau))
                                                     (rfs_vmetric V (tt - tau))
                                                     (gs (sub n) tau) (gamma tau) < eta)) /\
              !q. (!n. gs n tau0 = q) /\
                  (!gamma' eta. p2a_adm V tt x tau0 gamma' /\ gamma' tau0 = q /\ &0 < eta
                                ==> ?N. !n. N <= n
                                        ==> p2a_L_length V tt (gs n) tau0 <=
                                            p2a_L_length V tt gamma' tau0 + eta)
                  ==> p2a_min V tt x tau0 gamma /\ p2a_pc1 V tt gamma (&0) tau0 {} /\
                      gamma tau0 = q`;;

(* ------------------------------------------------------------------------- *)
(* C3. MT Cor 7.12 for smooth view settings, corrected: hypothesis (3) is   *)
(* replaced by attained slice minima and lower semicontinuity of the slice  *)
(* minimum of lx (what the comparison argument of Thm 7.10 needs; Part 3    *)
(* proves it as in MT Claim 16.25).                                         *)
(* ------------------------------------------------------------------------- *)

(* Hypothesis (2) asks x IN U s, as P2_COR_7_12_STATEMENT does (only the  *)
(* vertical path at x is used).                                           *)
let P2A_COR_7_12_VIEW_STATEMENT = new_definition
 `P2A_COR_7_12_VIEW_STATEMENT (u:A->bool) <=>
    !(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
     x tt a U r dt.
       p2a_svs V /\ a < tt /\ x IN topspace(rfs_vtop V tt) /\
       &0 < r /\ &0 < dt /\ p2a_region V (rfs_vball V tt x r) (tt - dt) tt /\
       p2a_st_open V U a tt /\
       (!t y. y IN U t ==> ?gamma. p2a_min V tt x (tt - t) gamma /\ gamma (tt - t) = y) /\
       (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
       (!t. a <= t /\ t < tt ==> ~(p2a_Lmin_set V tt x U t = {})) /\
       (!t e. a <= t /\ t < tt /\ &0 < e
              ==> ?d. &0 < d /\
                      !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                              ==> ?y. y IN U t /\
                                      p2a_lx V tt x (tt - t) y <=
                                      p2a_lx V tt x (tt - t') y' + e)
       ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ p2a_lx V tt x (tt - t) y <= &3 / &2`;;

(* ------------------------------------------------------------------------- *)
(* B. The history bridge: rfs_view hs is a smooth view setting whose        *)
(* persisting sets are regions (MT Prop 14.12; Lemma 14.11 across events),  *)
(* the P3 notions (rfs_L_adm, rfs_min_Lgeod, rfs_Lx, p3_st_compact,         *)
(* p3_st_open) agree with the view notions, a base point with an admissible *)
(* curve inside a compact smooth region is backward-smooth (a new cap point *)
(* on a core boundary sphere can start admissible curves but is not; such   *)
(* curves leave every compact smooth region), and the view infimum is      *)
(* honest (R bounded below on bounded time intervals).                       *)
(* ------------------------------------------------------------------------- *)

let P2A_HIST_VIEW_STATEMENT = new_definition
 `P2A_HIST_VIEW_STATEMENT (u:A->bool) <=>
    !hs:(A)rfs_history.
       rfs_history_ok hs
       ==> p2a_svs (rfs_view hs) /\
           (!t. compact_space (rfs_top_at hs t)) /\
           (!W a b. &0 <= a /\ a < b /\ b < rfs_horizon hs /\
                    rfs_persists (rfs_view hs) W a b
                    ==> p2a_region (rfs_view hs) W a b) /\
           (!y t. &0 < t /\ rfs_smooth_pt hs y t ==> p2a_smooth (rfs_view hs) y t) /\
           (!tt x b gamma. b < tt /\ rfs_L_adm hs tt x b gamma
                           ==> p2a_adm (rfs_view hs) tt x b gamma) /\
           (!tt x b gamma K. b < tt /\ rfs_L_adm hs tt x b gamma /\
                             p3_st_compact hs K /\
                             (!tau. &0 < tau /\ tau <= b ==> gamma tau IN K (tt - tau))
                             ==> p2a_bsmooth (rfs_view hs) x tt) /\
           (!tt x b gamma. b < tt /\ p2a_adm (rfs_view hs) tt x b gamma
                           ==> p2a_Lx (rfs_view hs) tt x b (gamma b) <=
                               p2a_L_length (rfs_view hs) tt gamma b) /\
           (!tt x b gamma. b < tt /\ p2a_adm1 (rfs_view hs) tt x b gamma
                           ==> rfs_L_adm hs tt x b gamma) /\
           (!tt x b gamma. b < tt /\ rfs_min_Lgeod hs tt x b gamma
                           ==> p2a_min (rfs_view hs) tt x b gamma) /\
           (!tt x b gamma. b < tt /\ p2a_min (rfs_view hs) tt x b gamma /\
                           p2a_pc1 (rfs_view hs) tt gamma (&0) b {}
                           ==> rfs_min_Lgeod hs tt x b gamma) /\
           (!tt x b q. b < tt /\ (?gamma. rfs_L_adm hs tt x b gamma /\ gamma b = q)
                       ==> rfs_Lx hs tt x b q = p2a_Lx (rfs_view hs) tt x b q) /\
           (!K. p3_st_compact hs K ==> p2a_cbox (rfs_view hs) K) /\
           (!U a b. p3_st_open hs U a b ==> p2a_st_open (rfs_view hs) U a b)`;;

(* ------------------------------------------------------------------------- *)
(* F. The corrected texts of P2_LEMMA_7_2 and P2_COR_7_12 (each implied by  *)
(* its original) are the statements of pc_p3_iface.ml under the original    *)
(* names; the bridges to them are P2A_T2_FIX and P2A_T3_FIX of              *)
(* pc_p2a_defs3.                                                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* D. The comparison lemma of the proof of MT Thm 7.10 (Dini form,          *)
(* P2A_DINI, proved below): a lower semicontinuous f on (0,T] with          *)
(* D^+ f(t) <= (c - f t)/t and f <= c near 0 satisfies f <= c.              *)
(* ------------------------------------------------------------------------- *)

let P2A_DINI_STATEMENT = new_definition
 `P2A_DINI_STATEMENT <=>
    !f c Tm.
       &0 < Tm /\
       (!t e. &0 < t /\ t <= Tm /\ &0 < e
              ==> ?d. &0 < d /\
                      !t'. &0 < t' /\ t' <= Tm /\ abs(t' - t) < d ==> f t <= f t' + e) /\
       (!t e. &0 < t /\ t < Tm /\ &0 < e
              ==> ?d. &0 < d /\
                      !t'. t < t' /\ t' < t + d /\ t' <= Tm
                           ==> f t' - f t <= ((c - f t) / t + e) * (t' - t)) /\
       (?t0. &0 < t0 /\ !t. &0 < t /\ t < t0 /\ t <= Tm ==> f t <= c)
       ==> !t. &0 < t /\ t <= Tm ==> f t <= c`;;

(* ------------------------------------------------------------------------- *)
(* O. Route obligations (the MT proofs as used; each is an implication      *)
(* between statement constants, proved in the pc_p2a files).  P2A_T1 (C1    *)
(* and the bridge give P2_THM_8_1) is proved below.                         *)
(* ------------------------------------------------------------------------- *)





(* O3 (MT Prop 14.12 locally, Lemma 14.11; the agreement of the P3 and view *)
(* notions needs honest infima (P2A_REQ_RLOWER_STATEMENT) and corner        *)
(* smoothing).                                                              *)
let P2A_ROUTE_BRIDGE_STATEMENT = new_definition
 `P2A_ROUTE_BRIDGE_STATEMENT (u:A->bool) <=>
    P3_LEMMA_14_11_STATEMENT u /\ P2A_REQ_RLOWER_STATEMENT u /\
    P2A_SMOOTHING_STATEMENT u
    ==> P2A_HIST_VIEW_STATEMENT u`;;

(* O4 (MT Thm 8.1 via Prop 8.2, Lemmas 8.3, 8.9 on the set of initial      *)
(* vectors of minimizers to B).                                              *)
let P2A_ROUTE_8_1_STATEMENT = new_definition
 `P2A_ROUTE_8_1_STATEMENT (u:A->bool) <=>
    P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_LGEOD_STATEMENT u /\
    P2A_MIN_RESTRICT_STATEMENT u /\ P2A_INJ_STATEMENT u /\
    P2A_RVI_MONO_STATEMENT u /\ P2A_RVI_ASYMP_STATEMENT u /\
    P2A_LX_USC_STATEMENT u /\ P2A_PARABOLIC_STATEMENT u /\
    P2A_SMALLZ_STATEMENT u /\ P2A_GAUSS_TAIL_STATEMENT /\
    P2A_REQ_AREA_STATEMENT u /\ P2A_REQ_VOLCMP_STATEMENT u
    ==> P2A_THM_8_1_VIEW_STATEMENT u`;;

(* O5 (MT Claim 8.5: Shi rescaled, metric comparison from the flow).        *)
let P2A_ROUTE_PARABOLIC_STATEMENT = new_definition
 `P2A_ROUTE_PARABOLIC_STATEMENT (u:A->bool) <=>
    P2A_REQ_SHI_SCALED_STATEMENT u ==> P2A_PARABOLIC_STATEMENT u`;;

(* O6 (MT Lemma 6.60, Claims 8.6-8.7).                                      *)
let P2A_ROUTE_SMALLZ_STATEMENT = new_definition
 `P2A_ROUTE_SMALLZ_STATEMENT (u:A->bool) <=>
    P2A_PARABOLIC_STATEMENT u /\ P2A_LGEOD_FLOW_STATEMENT u
    ==> P2A_SMALLZ_STATEMENT u`;;

(* O7 (regularity of minimizers by local uniqueness).                       *)
let P2A_ROUTE_MIN_LGEOD_STATEMENT = new_definition
 `P2A_ROUTE_MIN_LGEOD_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u
    ==> P2A_MIN_LGEOD_STATEMENT u`;;

(* O8 (corner lemma, MT Prop 6.30 first half).                               *)
let P2A_ROUTE_INJ_STATEMENT = new_definition
 `P2A_ROUTE_INJ_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_LGEOD_FLOW_STATEMENT u /\
    P2A_MIN_LGEOD_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u
    ==> P2A_INJ_STATEMENT u`;;

(* O9 (upper semicontinuity of Lx from the local boundary value problem).   *)
let P2A_ROUTE_LX_USC_STATEMENT = new_definition
 `P2A_ROUTE_LX_USC_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_SMOOTHING_STATEMENT u ==> P2A_LX_USC_STATEMENT u`;;

(* O10 (MT Lemma 7.2 by broken L-geodesics, Prop 16.21(1)-(2)).              *)
let P2A_ROUTE_LEMMA_7_2_STATEMENT = new_definition
 `P2A_ROUTE_LEMMA_7_2_STATEMENT (u:A->bool) <=>
    P2A_LOC_BVP_STATEMENT /\ P2A_SMOOTHING_STATEMENT u /\
    P2A_LGEOD_FLOW_STATEMENT u /\ P2A_MIN_LGEOD_STATEMENT u
    ==> P2A_LEMMA_7_2_VIEW_STATEMENT u`;;

(* O11 (MT Thm 7.10 / Cor 7.12: barrier at slice minima and the Dini        *)
(* comparison; the small-time bound from the vertical curve at x).          *)
let P2A_ROUTE_COR_7_12_STATEMENT = new_definition
 `P2A_ROUTE_COR_7_12_STATEMENT (u:A->bool) <=>
    P2A_BARRIER_STATEMENT u /\ P2A_MIN_RESTRICT_STATEMENT u /\ P2A_DINI_STATEMENT
    ==> P2A_COR_7_12_VIEW_STATEMENT u`;;

(* Obligation of the P2A bridge: histories have smooth transitions.  With   *)
(* P2C_HISTORY_REGULAR_STATEMENT this gives the region clause of            *)
(* P2A_HIST_VIEW_STATEMENT through P2A_REGULAR_REGION.                      *)

let P2A_HIST_TRANS_STATEMENT = new_definition
 `P2A_HIST_TRANS_STATEMENT (u:A->bool) <=>
    !hs:(A)rfs_history. rfs_history_ok hs ==> p2a_smooth_trans (rfs_view hs)`;;

(* ========================================================================= *)
(* Proved lemmas.  The P3 L-length is the view L-length of rfs_view hs;     *)
(* nonempty history slices are live; a junk-free minimizer realizes the     *)
(* L-distance; smooth points lie at positive times; P2A_T1: the view-level  *)
(* core of Thm 8.1 and the history bridge give P2_THM_8_1_STATEMENT;        *)
(* P2A_DINI: the comparison lemma behind MT Thm 7.10 / Cor 7.12.            *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;


(* The generic views of section D0 agree with the 3-d notions.              *)

let P2A_VIEW_PROJ_3 = prove
 (`!V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3).
     p2a_vtop V = rfs_vtop V /\ p2a_vatlas V = rfs_vatlas V /\
     p2a_vmetric V = rfs_vmetric V`,
  REWRITE_TAC[FORALL_PAIR_THM; p2a_vtop; p2a_vatlas; p2a_vmetric;
              rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2A_PERSISTS_3 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b. p2a_persists V W a b <=> rfs_persists V W a b`,
  REWRITE_TAC[FORALL_PAIR_THM; p2a_persists; rfs_persists]);;

let P2A_FLOW_VIEW_3 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) J g.
     p2a_flow_view (top,atlas) J g = rfs_flow_view (top,atlas) J g`,
  REWRITE_TAC[p2a_flow_view; rfs_flow_view]);;

let P2A_FLOW_UPTO_3 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) a b g.
     p2a_flow_upto (top,atlas) a b g <=> rfs_flow_upto (top,atlas) a b g`,
  REWRITE_TAC[p2a_flow_upto; rfs_flow_upto]);;

let P2A_PERSISTS_ALT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    W a b. p2a_persists V W a b <=>
           !s. a < s /\ s <= b
               ==> smooth_manifold_atlas (p2a_vtop V s) (p2a_vatlas V s) /\
                   open_in (p2a_vtop V s) W`,
  REWRITE_TAC[FORALL_PAIR_THM; p2a_persists; p2a_vtop; p2a_vatlas]);;

let P2A_RFS_VIEW_COMPONENTS = prove
 (`!hs:(A)rfs_history.
     rfs_vtop (rfs_view hs) = rfs_top_at hs /\
     rfs_vatlas (rfs_view hs) = rfs_atlas_at hs /\
     rfs_vmetric (rfs_view hs) = rfs_metric_at hs`,
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2A_L_LENGTH_VIEW = prove
 (`!(hs:(A)rfs_history) tt gamma b.
     rfs_L_length hs tt gamma b = p2a_L_length (rfs_view hs) tt gamma b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_L_length; p2a_L_length] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; rfs_L_integrand; p2a_L_integrand;
              rfs_view; p2a_vatlas; p2a_vmetric]);;

let P2A_TOPSPACE_LIVE = prove
 (`!(hs:(A)rfs_history) t x.
     x IN topspace(rfs_top_at hs t) ==> &0 <= t /\ t < rfs_horizon hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_top_at; rfs_horizon] THEN
  COND_CASES_TAC THEN REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t` THEN
  REWRITE_TAC[rfs_live] THEN MESON_TAC[]);;

let P2A_MIN_LX = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x b gamma.
     p2a_min V tt x b gamma
     ==> p2a_Lx V tt x b (gamma b) = p2a_L_length V tt gamma b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_min; p2a_Lx] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_INF_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `b':real` THEN DISCH_TAC THEN
  EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]);;

let P2A_T1 = prove
 (`!u:A->bool. P2A_THM_8_1_VIEW_STATEMENT u /\ P2A_HIST_VIEW_STATEMENT u
               ==> P2_THM_8_1_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_THM_8_1_VIEW_STATEMENT; P2_THM_8_1_STATEMENT] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`taub:real`; `l0:real`; `V0:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`taub:real`; `l0:real`; `V0:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kappa:real` THEN
  STRIP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `x:A`; `tt:real`; `r:real`; `tau0:real`;
                       `B:A->bool`; `K:real->A->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `x:A`; `tt:real`;
                                `r:real`; `tau0:real`; `B:A->bool`]) THEN
  REWRITE_TAC[P2A_RFS_VIEW_COMPONENTS] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `P2A_HIST_VIEW_STATEMENT (u:A->bool)` THEN
  REWRITE_TAC[P2A_HIST_VIEW_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= tt /\ tt < rfs_horizon (hs:(A)rfs_history)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[P2A_TOPSPACE_LIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `rfs_parabolic_exists (rfs_view (hs:(A)rfs_history)) tt x r (r pow 2)` THEN
    REWRITE_TAC[rfs_parabolic_exists] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
    ASM_REWRITE_TAC[CLOSED_IN_CLOSURE_OF];
    ASM_MESON_TAC[];
    X_GEN_TAC `q:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?gamma:real->A. rfs_min_Lgeod (hs:(A)rfs_history) tt x tau0 gamma /\
                                  gamma tau0 = q /\ rfs_lx hs tt x tau0 q <= l0`
      (X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM P2A_L_LENGTH_VIEW] THEN
    UNDISCH_TAC `rfs_min_Lgeod (hs:(A)rfs_history) tt x tau0 gamma` THEN
    REWRITE_TAC[rfs_min_Lgeod] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_lx (hs:(A)rfs_history) tt x tau0 q <= l0` THEN
    REWRITE_TAC[rfs_lx] THEN
    SUBGOAL_THEN `&0 < &2 * sqrt tau0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; SQRT_POS_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC]);;

let P2A_SMOOTH_PT_POS = prove
 (`!(hs:(A)rfs_history) y t. rfs_smooth_pt hs y t ==> &0 < t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_smooth_pt; rfs_view; rfs_persists] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - eta / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_top_at; rfs_live] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[]);;

let P2A_MIN_LGEOD_LT = prove
 (`!(hs:(A)rfs_history) tt x b gamma. rfs_min_Lgeod hs tt x b gamma ==> &0 < b /\ b < tt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rfs_min_Lgeod; rfs_L_adm] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < tt - b` MP_TAC THENL
   [MATCH_MP_TAC P2A_SMOOTH_PT_POS THEN
    EXISTS_TAC `hs:(A)rfs_history` THEN EXISTS_TAC `(gamma:real->A) b` THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2A_PERSISTS_MONO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a a' b. rfs_persists V W a b /\ a <= a' ==> rfs_persists V W a' b`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_persists] THEN
  MESON_TAC[REAL_LET_TRANS]);;

let P2A_CBOX_ST_COMPACT = prove
 (`!(hs:(A)rfs_history) K. p2a_cbox (rfs_view hs) K ==> p3_st_compact hs K`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2a_cbox; p3_st_compact; P2A_VIEW_PROJ_3; P2A_RFS_VIEW_COMPONENTS] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[p2a_region; P2A_PERSISTS_3] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Dini comparison lemma.  sg = sup of the times <= ts where f <= c; on *)
(* (sg, ts] f > c; for every e > 0, w = sup of the times in [sg, ts] where  *)
(* f t <= f sg + e (t - sg) is ts (lower semicontinuity closes the set, the *)
(* Dini bound pushes past w), so f ts <= f sg + e (ts - sg) for all e.       *)
(* ------------------------------------------------------------------------- *)

let P2A_DINI = prove
 (`P2A_DINI_STATEMENT`,
  REWRITE_TAC[P2A_DINI_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`f:real->real`; `c:real`; `Tm:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "lsc")
    (CONJUNCTS_THEN2 (LABEL_TAC "dp") (X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC)))) THEN
  X_GEN_TAC `ts:real` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?sg. &0 < sg /\ sg <= ts /\ (f:real->real) sg <= c /\
                    (!t. sg < t /\ t <= ts ==> c < f t)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `{t | &0 < t /\ t <= ts /\ (f:real->real) t <= c}` SUP) THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `min (t0 / &2) (ts / &2)` THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `ts:real` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SPEC_TAC(`sup {t | &0 < t /\ t <= ts /\ (f:real->real) t <= c}`, `sg:real`) THEN
    X_GEN_TAC `sg:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
    EXISTS_TAC `sg:real` THEN
    SUBGOAL_THEN `&0 < sg` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min (t0 / &2) (ts / &2)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ub" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `sg <= ts` ASSUME_TAC THENL
     [USE_THEN "lub" MATCH_MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      REMOVE_THEN "lsc" (MP_TAC o SPECL [`sg:real`; `((f:real->real) sg - c) / &2`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
      USE_THEN "lub" (MP_TAC o SPEC `sg - d`) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `y <= sg` ASSUME_TAC THENL
       [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "near" (MP_TAC o SPEC `y:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `t <= sg` MP_TAC THENL
       [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sg < ts` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. &0 < e ==> (f:real->real) ts <= f sg + e * (ts - sg)` MP_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `{t | sg <= t /\ t <= ts /\ (f:real->real) t <= f sg + e * (t - sg)}` SUP) THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [EXISTS_TAC `sg:real` THEN ASM_REAL_ARITH_TAC;
                      EXISTS_TAC `ts:real` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SPEC_TAC(`sup {t | sg <= t /\ t <= ts /\ (f:real->real) t <= f sg + e * (t - sg)}`,
             `w:real`) THEN
    X_GEN_TAC `w:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ubw") (LABEL_TAC "lubw")) THEN
    SUBGOAL_THEN `sg <= w /\ w <= ts` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "ubw" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        USE_THEN "lubw" MATCH_MP_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real->real) w <= f sg + e * (w - sg)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "lsc" (MP_TAC o SPECL
        [`w:real`; `((f:real->real) w - (f sg + e * (w - sg))) / &2`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nearw"))) THEN
      USE_THEN "lubw" (MP_TAC o SPEC `w - d`) THEN
      ANTS_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `y:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `y <= w` ASSUME_TAC THENL
       [USE_THEN "ubw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN `e * (y - sg) <= e * (w - sg)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "nearw" (MP_TAC o SPEC `y:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_CASES_TAC `(w:real) < ts` THENL
     [ALL_TAC;
      SUBGOAL_THEN `(w:real) = ts` (fun th -> ASM_MESON_TAC[th]) THEN ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `c <= (f:real->real) w` THENL
     [USE_THEN "dp" (MP_TAC o SPECL [`w:real`; `e / &2`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dpw"))) THEN
      ABBREV_TAC `t' = min (w + d / &2) ts` THEN
      SUBGOAL_THEN `w < t' /\ t' < w + d /\ t' <= ts` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "t'" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "dpw" (MP_TAC o SPEC `t':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(c - (f:real->real) w) / w <= &0` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 < w` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
        `((c - (f:real->real) w) / w + e / &2) * (t' - w) <= (e / &2) * (t' - w)`
        ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= e * (t' - w)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ubw" (MP_TAC o SPEC `t':real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real) = sg` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th))) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "dp" (MP_TAC o SPECL [`sg:real`; `&1`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dps"))) THEN
    ABBREV_TAC `M = (c - (f:real->real) sg) / sg + &1` THEN
    SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC
      `h = min (d / &2) (min ((ts - sg) / &2) ((c - (f:real->real) sg) / (&2 * M)))` THEN
    SUBGOAL_THEN `&0 < h /\ h < d /\ h <= ts - sg /\ M * h <= (c - (f:real->real) sg) / &2`
      STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < (c - (f:real->real) sg) / (&2 * M)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `h <= (c - (f:real->real) sg) / (&2 * M)` ASSUME_TAC THENL
       [EXPAND_TAC "h" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `M * (c - (f:real->real) sg) / (&2 * M)` THEN CONJ_TAC THENL
         [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < M` THEN
          CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    USE_THEN "dps" (MP_TAC o SPEC `sg + h`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(sg + h) - sg = h`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `sg + h` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `c:real`)) (concl th) &&
        not (can (find_term (fun t -> t = `Tm:real`)) (concl th)) &&
        not (can (find_term (fun t -> t = `t0:real`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `((f:real->real) ts - c) / (&2 * (ts - sg))`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((f:real->real) ts - c) / (&2 * (ts - sg)) * (ts - sg) = (f ts - c) / &2`
    SUBST1_TAC THENL
   [UNDISCH_TAC `sg < ts` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Teeth tests on the static flat view of real^3 (MT Example 6.3): the      *)
(* L-geodesic system is A' = 0, and the straight s-line tau |-> x + 2       *)
(* sqrt(tau) Z from x has L-length 2 |Z|^2 sqrt b over [0,b] (so            *)
(* l~ = |Z|^2, MT Example 6.76).                                            *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

let P2A_LRICCI_FLAT = prove
 (`!(A:real^N^N) y v w. lricci (\z. A) y v w = &0`,
  REWRITE_TAC[lricci; LRIEMANN_FLAT; VEC_COMPONENT; SUM_0]);;

let P2A_LSCALAR_FLAT = prove
 (`!(A:real^N^N) y. lscalar (\z. A) y = &0`,
  REWRITE_TAC[lscalar; P2A_LRICCI_FLAT; REAL_MUL_RZERO; SUM_0]);;

let P2A_LACC_FLAT = prove
 (`!tt s (y:real^3) (A:real^3). p2a_lacc (\t:real z:real^3. mat 1) tt s y A = vec 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[p2a_lacc; p2a_lgradR; p2a_lricop; GEOL_CHRISTOFFEL_CONST;
              P2A_LRICCI_FLAT; P2A_LSCALAR_FLAT; LIFT_NUM;
              FRECHET_DERIVATIVE_CONST_AT; VEC_COMPONENT; DROP_VEC] THEN
  REWRITE_TAC[VECTOR_ARITH `(lambda k. &0):real^N = vec 0`] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO; VECTOR_MUL_RZERO; VECTOR_NEG_0;
              VECTOR_ADD_LID; VECTOR_SUB_REFL]);;

let P2A_FLAT_LINE_VDERIV = prove
 (`!(x:real^3) (Z:real^3) tau.
     &0 < tau
     ==> ((\s. x + (&2 * sqrt(drop s)) % Z) has_vector_derivative (inv(sqrt tau) % Z))
         (at (lift tau))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s:real^1. lift(&2 * sqrt(drop s))) has_vector_derivative
                 lift(inv(sqrt tau))) (at (lift tau))` ASSUME_TAC THENL
   [SUBGOAL_THEN `((\t. &2 * sqrt t) has_real_derivative inv(sqrt tau)) (atreal tau)`
      MP_TAC THENL
     [SUBGOAL_THEN `inv(sqrt tau) = &2 * inv(&2 * sqrt tau)` SUBST1_TAC THENL
       [SUBGOAL_THEN `&0 < sqrt tau` MP_TAC THENL
         [ASM_SIMP_TAC[SQRT_POS_LT]; CONV_TAC REAL_FIELD];
        MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
        ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT]];
      REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; o_DEF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^1 v:real^3. drop u % v`;
                 `\s:real^1. lift(&2 * sqrt(drop s))`; `\s:real^1. (Z:real^3)`;
                 `lift(inv(sqrt tau))`; `vec 0:real^3`; `lift tau`]
    HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; BILINEAR_DROP_MUL; LIFT_DROP] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. (x:real^3)`; `vec 0:real^3`;
                 `\s:real^1. (&2 * sqrt(drop s)) % (Z:real^3)`;
                 `inv(sqrt tau) % (Z:real^3)`; `at (lift tau)`]
    HAS_VECTOR_DERIVATIVE_ADD) THEN
  ASM_REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; VECTOR_ADD_LID]);;

let P2A_L_LENGTH_FLAT = prove
 (`!J tt (x:real^3) (Z:real^3) b.
     &0 < b
     ==> p2a_L_length (rfs_flow_view (euclidean,open_set_atlas (:real^3)) J
                                     (\t:real y:real^3. mat 1))
                      tt (\tau. x + (&2 * sqrt tau) % Z) b =
         &2 * (Z dot Z) * sqrt b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_length] THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE_FINITE THEN
  MAP_EVERY EXISTS_TAC [`\tau. ((Z:real^3) dot Z) * inv(sqrt tau)`; `{&0, b}`] THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN
    REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < tau /\ tau < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(INST_TYPE [`:3`,`:N`] GEOL_EUCLID_FACTS) THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_local (open_set_atlas (:real^3)) ((:real^3),(\x:real^3. x))
                    (\x. mat 1) = (\y. mat 1)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    REWRITE_TAC[p2a_L_integrand; rfs_flow_view; p2a_vatlas; p2a_vmetric;
                mfd_scalar; mfd_speed; mfd_velocity] THEN
    ASM_REWRITE_TAC[P2A_LSCALAR_FLAT; MATRIX_VECTOR_MUL_LID; REAL_ADD_LID] THEN
    MP_TAC(SPECL [`x:real^3`; `Z:real^3`; `tau:real`] P2A_FLAT_LINE_VDERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `vector_derivative (\s. x + (&2 * sqrt(drop s)) % Z)
                         (at (lift tau) within interval[lift(&0),lift b]) =
       inv(sqrt tau) % (Z:real^3)` SUBST1_TAC THENL
     [MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
      ASM_SIMP_TAC[LIFT_DROP; IN_INTERVAL_1; HAS_VECTOR_DERIVATIVE_AT_WITHIN] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[SQRT_POW_2; DOT_POS_LE] THEN
    REWRITE_TAC[DOT_LMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `&0 < sqrt tau` MP_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * ((Z:real^3) dot Z) * sqrt b =
                (\t. &2 * (Z dot Z) * sqrt t) b - (\t. &2 * (Z dot Z) * sqrt t) (&0)`
    SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_SQRT];
    X_GEN_TAC `tau:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `((Z:real^3) dot Z) * inv(sqrt tau) = &2 * (Z dot Z) * inv(&2 * sqrt tau)`
      SUBST1_TAC THENL
     [SUBGOAL_THEN `&0 < sqrt tau` MP_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT]; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_SQRT]]);;

