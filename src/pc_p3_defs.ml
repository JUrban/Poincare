(* ========================================================================= *)
(* Unit pc_p3_defs: definitions of Part 3 (MT Ch 13-17) that               *)
(* do not involve the invariant: time steps T_j = 2^j/32 and step functions, *)
(* parameter sequences, the surgery scale function, cap modulus, truncation *)
(* of views, smooth points, flows smooth up to b, the standard initial     *)
(* metric and standard flows, kappa-solutions, geometric limits of flows,  *)
(* L-geometry of histories (D1-D6); the vocabulary of the route and of the *)
(* Part 1-2 interfaces (V1-V13).                                           *)
(* ========================================================================= *)

needs "src/pc_rfs_history.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D1. Time steps, step functions, parameter sequences, the surgery scale.   *)
(* ------------------------------------------------------------------------- *)

let p3_T = new_definition
 `p3_T (j:num) = &2 pow j / &32`;;

let p3_step = new_definition
 `p3_step (t:real) = minimal j. t < p3_T j`;;

let p3_stepf = new_definition
 `p3_stepf (s:num->real) (t:real) = s (p3_step t)`;;

let p3_seq_ok = new_definition
 `p3_seq_ok (s:num->real) <=> !j. &0 < s j /\ s (SUC j) <= s j`;;

let p3_seq_upto = new_definition
 `p3_seq_upto (i:num) (s:num->real) <=>
    !j. j <= i ==> &0 < s j /\ (j < i ==> s (SUC j) <= s j)`;;

(* The surgery scale function h(rho,delta) of MT Thm 11.31 (rho = delta r): *)
(* positive, h <= rho delta and h <= rho / 2C; the scale at time t.         *)

let p3_hfun = new_definition
 `p3_hfun (C:real) (hf:real->real->real) <=>
    !rho dl. &0 < rho /\ &0 < dl
             ==> &0 < hf rho dl /\ hf rho dl <= rho * dl /\
                 hf rho dl <= rho / (&2 * C)`;;

let p3_hscale = new_definition
 `p3_hscale (hf:real->real->real) (rp:real->real) (dl:real->real) (t:real) =
    hf (dl t * rp t) (dl t)`;;

(* A modulus for the closeness of surgery caps to the standard initial     *)
(* metric (the function delta1' of MT Thm 13.2(4)).                         *)

let p3_modulus = new_definition
 `p3_modulus (md:real->real) <=> !d. &0 < d ==> &0 < md d /\ md d <= d`;;

(* ------------------------------------------------------------------------- *)
(* D2. Views: components, truncation at a time, smooth points.               *)
(* ------------------------------------------------------------------------- *)

let rfs_trunc = new_definition
 `rfs_trunc (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
             G:real->A->real^3^3) (tau:real) =
    (\t. if t < tau then TM t else discrete_topology {}),
    (\t. if t < tau then AT t else {}),
    (\t. if t < tau then G t else (\x:A. mat 1))`;;

let rfs_vtop = new_definition
 `rfs_vtop (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
            G:real->A->real^3^3) = TM`;;

let rfs_vatlas = new_definition
 `rfs_vatlas (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
              G:real->A->real^3^3) = AT`;;

let rfs_vmetric = new_definition
 `rfs_vmetric (TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,
               G:real->A->real^3^3) = G`;;

(* Smooth points of the space-time of a history (MT: the open subset of     *)
(* smooth manifold points, Prop 14.12): x at time t persists in an open set *)
(* over (t - eta, t] for some eta > 0.  Exposed points (new cap points at   *)
(* an event time) and points of the initial slice are not smooth.          *)

let rfs_smooth_pt = new_definition
 `rfs_smooth_pt (hs:(A)rfs_history) (x:A) (t:real) <=>
    ?U eta. x IN U /\ &0 < eta /\ rfs_persists (rfs_view hs) U (t - eta) t`;;

(* A Ricci flow on (a,b], smooth up to b (the convention of ricci_flow_from *)
(* at the other end).                                                       *)

let rfs_flow_upto = new_definition
 `rfs_flow_upto (top:A topology,atlas:((A->bool)#(A->real^3))->bool)
                (a:real) (b:real) (g:real->A->real^3^3) <=>
    ricci_flow_on (top,atlas) a b g /\ riemannian_metric atlas (g b) /\
    !c. c IN atlas
        ==> ?e Fx. &0 < e /\
                   smooth_map_on
                     (interval(lift a,lift(b + e)) PCROSS IMAGE (SND c) (FST c)) Fx /\
                   !t y. a < t /\ t <= b /\ y IN IMAGE (SND c) (FST c)
                         ==> Fx(pastecart (lift t) y) =
                             (vectorize:real^3^3->real^(3,3)finite_prod)
                             (metric_local atlas c (g t) y)`;;

(* ------------------------------------------------------------------------- *)
(* D3. The standard initial metric (MT Def 12.1, Lemma 12.3, Ch 13 setup)    *)
(* on real^3 with the identity chart, tip vec 0; A0 is the radius beyond     *)
(* which the metric is the cylinder: in the neck coordinates p3_std_nc (s =  *)
(* A0 + 4 - d(0,x), direction x/|x|) it is cylinder_flow 0.  Partial and     *)
(* maximal standard Ricci flows (MT Def 12.4).                              *)
(* ------------------------------------------------------------------------- *)

let p3_std_dist = new_definition
 `p3_std_dist (g0:real^3->real^3^3) (x:real^3) =
    mfd_dist (euclidean,open_set_atlas (:real^3)) g0 (vec 0) x`;;

let p3_std_nc = new_definition
 `p3_std_nc (g0:real^3->real^3^3) (A0:real) (x:real^3) =
    exp((A0 + &4 - p3_std_dist g0 x) / sqrt(&2)) % (inv(norm x) % x)`;;

let p3_std_initial = new_definition
 `p3_std_initial (g0:real^3->real^3^3) (A0:real) <=>
    riemannian_metric (open_set_atlas (:real^3)) g0 /\
    mfd_complete (euclidean,open_set_atlas (:real^3)) g0 /\
    (!x u v. ~collinear {vec 0,u,v}
             ==> &0 <= mfd_sectional (open_set_atlas (:real^3)) g0 x u v) /\
    (!Q x. orthogonal_matrix Q /\ det Q = &1
           ==> transp Q ** g0 (Q ** x) ** Q = g0 x) /\
    (?r0. &0 < r0 /\
          !x u v. p3_std_dist g0 x < r0 /\ ~collinear {vec 0,u,v}
                  ==> mfd_sectional (open_set_atlas (:real^3)) g0 x u v = &1 / &4) /\
    &0 < A0 /\
    (!x. A0 < p3_std_dist g0 x
         ==> g0 x = mpullback (p3_std_nc g0 A0) (cylinder_flow (&0)) x)`;;

let p3_partial_std = new_definition
 `p3_partial_std (g0:real^3->real^3^3) (te:real) (G:real->real^3->real^3^3) <=>
    ricci_flow_from (euclidean,open_set_atlas (:real^3)) (&0) te G /\
    G (&0) = g0 /\
    (!t. &0 <= t /\ t < te ==> mfd_complete (euclidean,open_set_atlas (:real^3)) (G t)) /\
    (!t1. t1 < te
          ==> ?K. !t x. &0 <= t /\ t <= t1
                        ==> mfd_rm_norm (open_set_atlas (:real^3)) (G t) x <= K)`;;

let p3_std_flow = new_definition
 `p3_std_flow (g0:real^3->real^3^3) (te:real) (G:real->real^3->real^3^3) <=>
    p3_partial_std g0 te G /\
    ~(?te' G'. te < te' /\ p3_partial_std g0 te' G' /\
               !t. &0 <= t /\ t < te ==> G' t = G t)`;;

(* ------------------------------------------------------------------------- *)
(* D4. kappa-solutions (MT Def 9.2) on a manifold of carrier type B: an      *)
(* ancient Ricci flow (defined on (-inf,b) for some b > 0; slices t <= 0    *)
(* matter), connected complete slices, sec >= 0 (in dimension 3 this is     *)
(* Rm >= 0), bounded curvature on each slice, non-flat, kappa-noncollapsed  *)
(* on all scales.                                                           *)
(* ------------------------------------------------------------------------- *)

let p3_kappa_solution = new_definition
 `p3_kappa_solution (kappa:real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) <=>
    &0 < kappa /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    connected_space top /\ ~(topspace top = {}) /\
    (?b. &0 < b /\ !a. a < b ==> ricci_flow_on (top,atlas) a b g) /\
    (!t. t <= &0 ==> mfd_complete (top,atlas) (g t)) /\
    (!t x u v. t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional atlas (g t) x u v) /\
    (!t. t <= &0 ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
    (!t. t <= &0 ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g t) x) /\
    (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {t | t <= &0} g) kappa r0)`;;

(* ------------------------------------------------------------------------- *)
(* D5. Partial geometric limit Ricci flows of based, rescaled views (MT Def  *)
(* 5.12): views V k with base points x k at times t k, rescaled by Q k      *)
(* (metric Q G(t + s / Q), s in (-Tl, 0]); the limit is a Ricci flow on a  *)
(* manifold of carrier type B on (-Tl,0] based at xl; exhaustion W k,      *)
(* times ts k increasing to Tl, smooth embeddings phi k of W k into the     *)
(* slices (persisting), C^m convergence of the rescaled pullbacks on        *)
(* compact sets, uniformly on compact time intervals.                       *)
(* ------------------------------------------------------------------------- *)

let p3_flow_limit = new_definition
 `p3_flow_limit
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
    (xl:B) (Tl:real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
    &0 < Tl /\ (!k. &0 < Q k) /\
    (!a. --Tl < a /\ a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    ?W ts phi.
      (!k. open_in top (W k) /\ xl IN W k /\ compact_in top (top closure_of W k) /\
           top closure_of W k SUBSET W (SUC k)) /\
      UNIONS {W k | k IN (:num)} = topspace top /\
      (!k. &0 < ts k /\ ts k < Tl /\ ts k <= ts (SUC k)) /\
      (!a. a < Tl ==> ?k. a <= ts k) /\
      (!k. phi k xl = x k) /\
      (!k s. --(ts k) <= s /\ s <= &0
             ==> ?psi. mfd_diffeo top atlas (W k)
                         (rfs_vtop (V k) (t k + s / Q k)) (rfs_vatlas (V k) (t k + s / Q k))
                         (IMAGE (phi k) (W k)) (phi k) psi) /\
      (!K m eta a. compact_in top K /\ --Tl < a /\ a <= &0 /\ &0 < eta
                   ==> ?k0. !k. k0 <= k
                                ==> K SUBSET W k /\ --(ts k) <= a /\
                                    !s y. a <= s /\ s <= &0 /\ y IN K
                                          ==> lck_dist2 m
                                                (metric_local atlas (chart_at atlas y) (g s))
                                                (\z. Q k %%
                                                     rfs_pullback
                                                       (rfs_vatlas (V k) (t k + s / Q k))
                                                       (phi k o chart_inv (chart_at atlas y))
                                                       (rfs_vmetric (V k) (t k + s / Q k)) z)
                                                (SND(chart_at atlas y) y) < eta)`;;

(* ------------------------------------------------------------------------- *)
(* D6. L-geometry of a history (MT Ch 6, Def 6.2, 6.9; Ch 16): space-time  *)
(* curves gamma tau at time tt - tau (rfs_st_curve), admissible if smooth   *)
(* points for tau > 0 and of finite L-length; L-length; the L-distance     *)
(* Lx (inf over admissible curves); minimizing L-geodesics; the reduced     *)
(* length lx = Lx / 2 sqrt tau.                                             *)
(* ------------------------------------------------------------------------- *)

let rfs_L_integrand = new_definition
 `rfs_L_integrand (hs:(A)rfs_history) (tt:real) (gamma:real->A) (b:real) (tau:real) =
    sqrt tau *
    (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau)) (gamma tau) +
     mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
               gamma (&0) b tau pow 2)`;;

let rfs_L_length = new_definition
 `rfs_L_length (hs:(A)rfs_history) (tt:real) (gamma:real->A) (b:real) =
    real_integral (real_interval[&0,b]) (rfs_L_integrand hs tt gamma b)`;;

let rfs_L_adm = new_definition
 `rfs_L_adm (hs:(A)rfs_history) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    &0 < b /\ rfs_st_curve hs tt gamma (&0) b /\ gamma (&0) = x /\
    (!tau. &0 < tau /\ tau <= b ==> rfs_smooth_pt hs (gamma tau) (tt - tau)) /\
    rfs_L_integrand hs tt gamma b real_integrable_on real_interval[&0,b]`;;

let rfs_Lx = new_definition
 `rfs_Lx (hs:(A)rfs_history) (tt:real) (x:A) (b:real) (q:A) =
    inf {rfs_L_length hs tt gamma b | gamma |
         rfs_L_adm hs tt x b gamma /\ gamma b = q}`;;

let rfs_min_Lgeod = new_definition
 `rfs_min_Lgeod (hs:(A)rfs_history) (tt:real) (x:A) (b:real) (gamma:real->A) <=>
    rfs_L_adm hs tt x b gamma /\
    rfs_L_length hs tt gamma b = rfs_Lx hs tt x b (gamma b)`;;

let rfs_lx = new_definition
 `rfs_lx (hs:(A)rfs_history) (tt:real) (x:A) (b:real) (q:A) =
    rfs_Lx hs tt x b q / (&2 * sqrt b)`;;

(* ------------------------------------------------------------------------- *)
(* Vocabulary V1-V13 (the setting of MT Props 16.1-16.5 is in pc_p3_inv,   *)
(* it needs the step hypotheses).                                          *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* V1. Compact subsets of the smooth part of a history (MT Prop 14.12, Def  *)
(* 16.20): a space-time set K (slices K t) inside finitely many compact     *)
(* boxes C j x [a j, b j], each C j inside an open W j that persists over    *)
(* (a j - eta, b j] (so the box lies in the smooth part; boxes may cross    *)
(* event times through retained points).                                     *)
(* ------------------------------------------------------------------------- *)

let p3_st_compact = new_definition
 `p3_st_compact (hs:(A)rfs_history) (K:real->A->bool) <=>
    ?n W C a b eta.
      &0 < eta /\
      (!j:num. j < n
           ==> a j <= b j /\ (C j:A->bool) SUBSET W j /\
               rfs_persists (rfs_view hs) (W j) (a j - eta) (b j) /\
               !s. a j <= s /\ s <= b j ==> compact_in (rfs_top_at hs s) (C j)) /\
      (!t y. y IN K t ==> ?j. j < n /\ a j <= t /\ t <= b j /\ y IN C j)`;;

(* ------------------------------------------------------------------------- *)
(* V2. Backward flow lines: the flow line through y at time t is defined on *)
(* [s, t] (points are fixed along flow lines; an exposed point of an event  *)
(* at time te in (s, t] is not in the slices before te).                    *)
(* ------------------------------------------------------------------------- *)

let p3_flowline = new_definition
 `p3_flowline (hs:(A)rfs_history) (y:A) (s:real) (t:real) <=>
    s <= t /\ !s'. s <= s' /\ s' <= t ==> y IN topspace(rfs_top_at hs s')`;;

(* ------------------------------------------------------------------------- *)
(* V3. Pointwise notions in a view: a strong (C,eps)-canonical neighbourhood *)
(* at (x,t); kappa-noncollapsing at (x,t) on scales <= r0 without the       *)
(* positive-curvature exemption (MT Def 9.1 / 14.15, used by Thm 11.1, 11.8 *)
(* and Cor 9.95); |Rm| and |nabla^l Rm|^2 at (x,t).                           *)
(* ------------------------------------------------------------------------- *)

let p3_canon_at = new_definition
 `p3_canon_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                 (real->A->real^3^3)) (C:real) (eps:real) (x:A) (t:real) <=>
    ?U. rfs_strong_canonical V C eps x t U`;;

let p3_noncoll_at = new_definition
 `p3_noncoll_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (kappa:real) (r0:real) (x:A) (t:real) <=>
    !r. &0 < r /\ r <= r0 /\ rfs_parabolic_exists V t x r (r pow 2) /\
        (!s y. t - r pow 2 < s /\ s <= t /\ y IN rfs_vball V t x r
               ==> mfd_rm_norm (rfs_vatlas V s) (rfs_vmetric V s) y <= inv(r pow 2))
        ==> ?v. mfd_has_volume (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t)
                               (rfs_vball V t x r) v /\
                kappa * r pow 3 <= v`;;

(* KL Def 69.1 (c): the C-component alternative carries the volume clause   *)
(* Vol(U) > C^-1 R(x)^(-3/2); eps-round components need none (they are      *)
(* round S^3 by Killing-Hopf in simply connected stages, P3_PROP_16_3).     *)

let p3_comp_vol = new_definition
 `p3_comp_vol (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (C:real) (x:A) (t:real) (U:A->bool) <=>
    ?v. mfd_has_volume (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) U v /\
        inv C * inv(sqrt(rfs_vscalar V t x)) pow 3 < v`;;

let p3_strong_canonv = new_definition
 `p3_strong_canonv (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3))
                      (C:real) (eps:real) (x:A) (t:real) (U:A->bool) <=>
    (?e. rfs_strong_neck V eps x t e /\ U = IMAGE e (rfs_neck_dom eps)) \/
    (?Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C eps U Y /\ x IN Y) \/
    (x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U /\
     p3_comp_vol V C x t U) \/
    (x IN U /\ rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) eps U)`;;

let p3_canonv_at = new_definition
 `p3_canonv_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) (C:real) (eps:real) (x:A) (t:real) <=>
    ?U. p3_strong_canonv V C eps x t U`;;

let p3_canonv_assumption = new_definition
 `p3_canonv_assumption (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) (C:real) (eps:real) (rp:real->real) <=>
    !t x. &0 <= t /\ x IN topspace(rfs_vtop V t) /\
          inv(rp t pow 2) <= rfs_vscalar V t x
          ==> p3_canonv_at V C eps x t`;;

let p3_noncoll_all = new_definition
 `p3_noncoll_all (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) (kp:real->real) (r0:real) <=>
    !t x. &0 <= t /\ x IN topspace(rfs_vtop V t) ==> p3_noncoll_at V (kp t) r0 x t`;;

(* ---- weakening lemmas: canonv and noncoll_all imply the plain notions --- *)

let P3_STRONG_CANONV_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U.
     p3_strong_canonv V C eps x t U ==> rfs_strong_canonical V C eps x t U`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[p3_strong_canonv; rfs_strong_canonical; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  MESON_TAC[]);;

let P3_CANONV_AT_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t.
     p3_canonv_at V C eps x t ==> p3_canon_at V C eps x t`,
  REWRITE_TAC[p3_canonv_at; p3_canon_at] THEN MESON_TAC[P3_STRONG_CANONV_IMP]);;

let P3_CANONV_ASSUMPTION_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps rp.
     p3_canonv_assumption V C eps rp ==> rfs_canonical_assumption V C eps rp`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[p3_canonv_assumption; rfs_canonical_assumption; rfs_vtop; rfs_vscalar] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[p3_canonv_at] THEN MESON_TAC[P3_STRONG_CANONV_IMP]);;

let P3_NONCOLL_ALL_IMP = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    kp r0.
     p3_noncoll_all V kp r0 ==> rfs_noncollapsed V kp r0`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  REWRITE_TAC[p3_noncoll_all; rfs_noncollapsed; p3_noncoll_at; rfs_vtop; rfs_vatlas;
              rfs_vmetric] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "H") THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `r:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "H" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[]);;

let p3_vrm = new_definition
 `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) (t:real) (x:A) =
    mfd_rm_norm (rfs_vatlas V t) (rfs_vmetric V t) x`;;

let p3_vderiv2 = new_definition
 `p3_vderiv2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) (l:num) (t:real) (x:A) =
    lrm_deriv_norm2 l (metric_local (rfs_vatlas V t) (chart_at (rfs_vatlas V t) x)
                                    (rfs_vmetric V t))
                    (SND(chart_at (rfs_vatlas V t) x) x)`;;

(* ------------------------------------------------------------------------- *)
(* V4. Transport of a metric along a map psi of manifolds (A to B), in the   *)
(* preferred charts of the source: mfd_pullback_metric of pc_mfd_restrict   *)
(* (used for closeness via a map in Prop 9.79 and Thm 12.32 transfers).      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* V5. The singular time at the horizon of a history (MT Thm 11.19, Def     *)
(* 11.22, 11.27): Omega (liminf of R finite), the maximal extension view     *)
(* for a limit metric gl on Omega, Omega_rho.                                *)
(* ------------------------------------------------------------------------- *)

let p3_omega = new_definition
 `p3_omega (hs:(A)rfs_history) =
    {x | x IN topspace(hs_top hs (hs_count hs)) /\
         ?B. !t1. t1 < rfs_horizon hs
                  ==> ?t. t1 < t /\ hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs /\
                          mfd_scalar (hs_atlas hs (hs_count hs))
                                     (hs_metric hs (hs_count hs) t) x <= B}`;;

let p3_maxext = new_definition
 `p3_maxext (hs:(A)rfs_history) (Om:A->bool) (gl:A->real^3^3) =
    (\t. if t = rfs_horizon hs then subtopology (hs_top hs (hs_count hs)) Om
         else rfs_top_at hs t),
    (\t. if t = rfs_horizon hs then restrict_atlas (hs_atlas hs (hs_count hs)) Om
         else rfs_atlas_at hs t),
    (\t. if t = rfs_horizon hs
         then restrict_metric (hs_atlas hs (hs_count hs)) Om gl
         else rfs_metric_at hs t)`;;

let p3_omega_rho = new_definition
 `p3_omega_rho (atlas:((A->bool)#(A->real^3))->bool) (Om:A->bool)
               (gl:A->real^3^3) (rho:real) =
    {x | x IN Om /\ mfd_scalar atlas gl x <= inv(rho pow 2)}`;;

(* ------------------------------------------------------------------------- *)
(* V6. Strong eps-horns of the time-T slice of a view (MT Def 11.25): H      *)
(* parametrizes the region |y| > 1/2 of real^3 (S^2 x (-1, inf) radially;   *)
(* the horn is the image of |y| >= 1), proper on |y| >= 1, every horn point *)
(* the centre of a strong eps-neck, the boundary sphere the central sphere   *)
(* of a strong eps-neck.  p3_horn_end: the end cut off by the central sphere *)
(* of a neck e inside the horn (the component of the horn minus that sphere  *)
(* containing the plus side point e(2 basis 1)).                             *)
(* ------------------------------------------------------------------------- *)

let p3_horn = new_definition
 `p3_horn (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
             (real->A->real^3^3)) (th:real) (eps:real) (H:real^3->A) <=>
    mfd_param (rfs_vtop V th) (rfs_vatlas V th) {y | &1 / &2 < norm y} H /\
    (!K. compact_in (rfs_vtop V th) K ==> bounded {y | &1 <= norm y /\ H y IN K}) /\
    (!y. &1 <= norm y ==> ?e. rfs_strong_neck V eps (H y) th e) /\
    (?x e. rfs_strong_neck V eps x th e /\
           IMAGE e (sphere(vec 0,&1)) = IMAGE H (sphere(vec 0,&1)))`;;

let p3_horn_set = new_definition
 `p3_horn_set (H:real^3->A) = IMAGE H {y | &1 <= norm y}`;;

let p3_horn_end = new_definition
 `p3_horn_end (top:A topology) (H:real^3->A) (e:real^3->A) =
    connected_component_of
      (subtopology top (p3_horn_set H DIFF IMAGE e (sphere(vec 0,&1))))
      (e(&2 % basis 1))`;;

(* ------------------------------------------------------------------------- *)
(* V7. Based, rescaled sequences of histories (MT Thm 11.1 hypotheses (1)-  *)
(* (5) and Thm 11.8): Q n = R(x n, t n) -> infinity, pinching, canonical     *)
(* neighbourhoods above 4 Q n before t n, kappa-noncollapsing on scales      *)
(* <= r0 at the points of B(x n, t n, A Q n^(-1/2)), backward flow lines of  *)
(* length mu / max(Q n, R(y)) from those points.                              *)
(* ------------------------------------------------------------------------- *)

let p3_blowup_seq = new_definition
 `p3_blowup_seq (C:real,eps:real,kappa:real,r0:real,mu:real)
                (hs:num->(A)rfs_history) (x:num->A) (t:num->real) <=>
    &0 < kappa /\ &0 < r0 /\ &0 < mu /\
    (!n. rfs_history_ok (hs n) /\ rfs_pinched (rfs_view (hs n)) /\
         x n IN topspace(rfs_top_at (hs n) (t n))) /\
    (!B. ?N. !n. N <= n ==> B < rfs_vscalar (rfs_view (hs n)) (t n) (x n)) /\
    (!n y s. s <= t n /\ y IN topspace(rfs_top_at (hs n) s) /\
             &4 * rfs_vscalar (rfs_view (hs n)) (t n) (x n) <=
             rfs_vscalar (rfs_view (hs n)) s y
             ==> p3_canon_at (rfs_view (hs n)) C eps y s) /\
    (!A. ?N. !n y. N <= n /\
                   y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                          (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (t n) (x n))))
                   ==> p3_noncoll_at (rfs_view (hs n)) kappa r0 y (t n) /\
                       p3_flowline (hs n) y
                         (t n - mu * inv(max (rfs_vscalar (rfs_view (hs n)) (t n) (x n))
                                             (rfs_vscalar (rfs_view (hs n)) (t n) y)))
                         (t n))`;;

(* Thm 11.8 extra hypothesis for a backward time Tb (all Tb < T0): for    *)
(* every A, for n large, B(x n, t n, A Q n^(-1/2)) persists over             *)
(* (t n - Tb / Q n, t n] and its points at those times are kappa-noncollapsed *)
(* on scales <= r0.                                                           *)

let p3_blowup_back = new_definition
 `p3_blowup_back (kappa:real,r0:real) (hs:num->(A)rfs_history) (x:num->A)
                 (t:num->real) (Tb:real) <=>
    !A. ?N. !n. N <= n
                ==> rfs_persists (rfs_view (hs n))
                      (rfs_vball (rfs_view (hs n)) (t n) (x n)
                         (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (t n) (x n)))))
                      (t n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (t n) (x n))) (t n) /\
                    !s y. t n - Tb * inv(rfs_vscalar (rfs_view (hs n)) (t n) (x n)) < s /\
                          s <= t n /\
                          y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                 (A * inv(sqrt(rfs_vscalar (rfs_view (hs n)) (t n) (x n))))
                          ==> p3_noncoll_at (rfs_view (hs n)) kappa r0 y s`;;

(* ------------------------------------------------------------------------- *)
(* V8. Ricci flows on regions of a history: on the set W over (a, b] the     *)
(* family of the history is (after transport to the atlas of the slice at b) *)
(* a smooth Ricci flow on the open submanifold W (MT Prop 14.12 locally;     *)
(* within a slab this is the slab flow, across an event it is Lemma 14.11).  *)
(* ------------------------------------------------------------------------- *)

let p3_region_flow = new_definition
 `p3_region_flow (hs:(A)rfs_history) (W:A->bool) (a:real) (b:real) <=>
    rfs_persists (rfs_view hs) W a b /\
    rfs_flow_upto (subtopology (rfs_top_at hs b) W,
                   restrict_atlas (rfs_atlas_at hs b) W) a b
      (\s. restrict_metric (rfs_atlas_at hs b) W
             (\x. if s = b then rfs_metric_at hs b x
                  else mfd_pullback_metric (rfs_atlas_at hs b) (rfs_atlas_at hs s) (\y. y)
                                       (rfs_metric_at hs s) x))`;;

(* ------------------------------------------------------------------------- *)
(* V9. Subsequences; geometric limits of based rescaled time slices (MT Def *)
(* 5.3 and Thm 5.11) and of based rescaled flows on a time set J (MT Def    *)
(* 5.12 for J = (-T,0], and forward intervals [0,theta) as in Lemma 16.8):   *)
(* the limit (top,atlas,g) on carrier type B, base point xl, exhaustion W k, *)
(* embeddings phi k into the slices at t k (constant along flow lines),      *)
(* C^m convergence of Q k times the pulled back metrics at the times         *)
(* t k + s / Q k, uniformly on compact sets and compact time intervals.      *)
(* ------------------------------------------------------------------------- *)

let p3_subseq = new_definition
 `p3_subseq (sub:num->num) <=> !m n. m < n ==> sub m < sub n`;;

let p3_slice_limit = new_definition
 `p3_slice_limit
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) (xl:B) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
    riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\ (!k. &0 < Q k) /\
    ?W phi.
      (!k. open_in top (W k) /\ xl IN W k /\ compact_in top (top closure_of W k) /\
           top closure_of W k SUBSET W (SUC k)) /\
      UNIONS {W k | k IN (:num)} = topspace top /\
      (!k. phi k xl = x k) /\
      (!k. ?psi. mfd_diffeo top atlas (W k) (rfs_vtop (V k) (t k)) (rfs_vatlas (V k) (t k))
                            (IMAGE (phi k) (W k)) (phi k) psi) /\
      (!K m eta. compact_in top K /\ &0 < eta
                 ==> ?k0. !k. k0 <= k
                              ==> K SUBSET W k /\
                                  !y. y IN K
                                      ==> lck_dist2 m
                                            (metric_local atlas (chart_at atlas y) g)
                                            (\z. Q k %%
                                                 rfs_pullback (rfs_vatlas (V k) (t k))
                                                   (phi k o chart_inv (chart_at atlas y))
                                                   (rfs_vmetric (V k) (t k)) z)
                                            (SND(chart_at atlas y) y) < eta)`;;

let p3_flow_limit_on = new_definition
 `p3_flow_limit_on
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real) (J:real->bool)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
    (xl:B) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
    (&0) IN J /\ (!k. &0 < Q k) /\
    ?W phi.
      (!k. open_in top (W k) /\ xl IN W k /\ compact_in top (top closure_of W k) /\
           top closure_of W k SUBSET W (SUC k)) /\
      UNIONS {W k | k IN (:num)} = topspace top /\
      (!k. phi k xl = x k) /\
      (!a b K m eta. real_interval[a,b] SUBSET J /\ compact_in top K /\ &0 < eta
                     ==> ?k0. !k. k0 <= k
                                  ==> K SUBSET W k /\
                                      (!s. a <= s /\ s <= b
                                           ==> ?psi. mfd_diffeo top atlas (W k)
                                                 (rfs_vtop (V k) (t k + s / Q k))
                                                 (rfs_vatlas (V k) (t k + s / Q k))
                                                 (IMAGE (phi k) (W k)) (phi k) psi) /\
                                      !s y. a <= s /\ s <= b /\ y IN K
                                            ==> lck_dist2 m
                                                  (metric_local atlas (chart_at atlas y) (g s))
                                                  (\z. Q k %%
                                                       rfs_pullback
                                                         (rfs_vatlas (V k) (t k + s / Q k))
                                                         (phi k o chart_inv (chart_at atlas y))
                                                         (rfs_vmetric (V k) (t k + s / Q k)) z)
                                                  (SND(chart_at atlas y) y) < eta)`;;

(* ------------------------------------------------------------------------- *)
(* V10. Open subsets of the space-time of a history inside (a,b) (slices    *)
(* U t), contained in the smooth part (MT Prop 16.4, Cor 7.12): every point *)
(* has an open neighbourhood persisting over a time interval around t that  *)
(* lies in U at those times.                                                 *)
(* ------------------------------------------------------------------------- *)

let p3_st_open = new_definition
 `p3_st_open (hs:(A)rfs_history) (U:real->A->bool) (a:real) (b:real) <=>
    (!t y. y IN U t ==> a <= t /\ t < b) /\
    !t y. y IN U t
          ==> ?W eta. &0 < eta /\ y IN W /\
                      rfs_persists (rfs_view hs) W (t - eta) (t + eta) /\
                      !s. t - eta < s /\ s < t + eta /\ a <= s /\ s < b ==> W SUBSET U s`;;

(* ------------------------------------------------------------------------- *)
(* V11. Closeness of two views near two points, after rescaling: the        *)
(* metrics Q G(t + s/Q) on W and Q' psi-pullback of G'(t' + s/Q') are delta- *)
(* close in C^[1/delta] for every normalized time s in J (MT Prop 9.79, the *)
(* transfers from the rescaled standard solution in Lemmas 17.2 and 17.7).   *)
(* ------------------------------------------------------------------------- *)

let p3_view_close = new_definition
 `p3_view_close (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) (t:real) (Q:real) (W:A->bool)
                (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                    (real->B->real^3^3)) (t':real) (Q':real) (psi:A->B)
                (J:real->bool) (delta:real) <=>
    &0 < Q /\ &0 < Q' /\
    !s. s IN J
        ==> (?psi'. mfd_diffeo (rfs_vtop V (t + s / Q)) (rfs_vatlas V (t + s / Q)) W
                               (rfs_vtop V' (t' + s / Q')) (rfs_vatlas V' (t' + s / Q'))
                               (IMAGE psi W) psi psi') /\
            rfs_mclose (rfs_kreg delta) delta (rfs_vatlas V (t + s / Q)) W
              (\y. Q %% rfs_vmetric V (t + s / Q) y)
              (\y. Q' %% mfd_pullback_metric (rfs_vatlas V (t + s / Q))
                                         (rfs_vatlas V' (t' + s / Q')) psi
                                         (rfs_vmetric V' (t' + s / Q')) y)`;;

(* ------------------------------------------------------------------------- *)
(* V12. Standard initial metric: the radial map of MT Claim 13.1 / Lemma     *)
(* 12.37 from neck coordinates (s = sqrt 2 log|y|) to the model: the point   *)
(* with the same direction and s1 = A0 + 4 - d(0,x) = s, the tip for         *)
(* s >= A0 + 4 (only Lipschitz there); the minimizing set of                *)
(* L on a slice of a space-time set U (MT Prop 16.4(4), Cor 7.12(3)).       *)
(* ------------------------------------------------------------------------- *)

let p3_std_radial = new_definition
 `p3_std_radial (g0:real^3->real^3^3) (A0:real) (y:real^3) =
    if A0 + &4 <= sqrt(&2) * log(norm y) then vec 0
    else @x:real^3. ~(x = vec 0) /\ inv(norm x) % x = inv(norm y) % y /\
                    A0 + &4 - p3_std_dist g0 x = sqrt(&2) * log(norm y)`;;

let p3_Lmin_set = new_definition
 `p3_Lmin_set (hs:(A)rfs_history) (tt:real) (x:A) (U:real->A->bool) (t:real) =
    {y | y IN U t /\ !z. z IN U t ==> rfs_Lx hs tt x (tt - t) y <= rfs_Lx hs tt x (tt - t) z}`;;

(* ------------------------------------------------------------------------- *)
(* V13. Energies of backward-time curves (MT Prop 16.13: the integral of    *)
(* R + |X|^2; Lemma 16.15: L_plus with R_plus = max(R,0)), and the setting  *)
(* of MT Props 16.1-16.5 at step i: the step hypotheses with control bound  *)
(* dlt, the new parameter r' = rs'(i+1), strong canonical neighbourhoods     *)
(* with rs' on the whole history.                                            *)
(* ------------------------------------------------------------------------- *)

let p3_energy = new_definition
 `p3_energy (hs:(A)rfs_history) (tt:real) (gamma:real->A) (b:real) =
    real_integral (real_interval[&0,b])
      (\tau. mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau)) (gamma tau) +
             mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                       gamma (&0) b tau pow 2)`;;

let p3_Lplus = new_definition
 `p3_Lplus (hs:(A)rfs_history) (tt:real) (gamma:real->A) (b:real) =
    real_integral (real_interval[&0,b])
      (\tau. sqrt tau *
             (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                   (gamma tau)) +
              mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                        gamma (&0) b tau pow 2))`;;

