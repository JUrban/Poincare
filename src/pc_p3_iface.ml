(* ========================================================================= *)
(* Unit pc_p3_iface: the Part 1-2 interface statements of Part 3, i.e.       *)
(* exactly the Part 1-2 results that the MT Ch 13-17 proofs use, in the      *)
(* forms used (prefix P2_; u fixes the carrier type, w that of geometric     *)
(* limits), with the scaling input P2_NORMALIZE and, through pc_pde_iface,   *)
(* the PDE statements for MT Thm 3.11, Prop 3.12, Prop 4.11 (curvature       *)
(* part) and Prop 4.12.  Statements only.  Where MT's statement needs a      *)
(* correction, the body is the corrected statement of the Part 2 units:      *)
(* P2_THM_5_15, P2_LEMMA_11_2, P2_LEMMA_11_23, P2_THM_11_8, P2_LEMMA_11_30,  *)
(* P2_THM_11_31 and P2_THM_12_32 (Part 2C), P2_LEMMA_7_2 and P2_COR_7_12     *)
(* (Part 2A), P2_PROP_2_19, P2_PROP_9_79_SLICE, P2_PROP_9_79_NECK,           *)
(* P2_COR_9_95 and P2_THM_10_2 (Part 2B).  Added statements: P2C_PROP_5_14   *)
(* (forward limits keeping the cap maps and the initial slice, for Lemma     *)
(* 16.8), P2C_HISTORY_REGULAR and P2C_FLOW_VIEW_REGULAR with the Part 2C     *)
(* vocabulary they use, and P2_PROP_2_19_SEP (the route form, p. 407),       *)
(* P2_PROP_9_79_OPEN (p. 396) and P2_SEP_LIMIT with the Part 2B vocabulary   *)
(* p2b_kappa_solution and p2b_hs_sep.                                        *)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;
needs "src/pc_pde_iface.ml";;
needs "src/pc_apx_sep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* S0. Normalization by scaling (MT p. 353, Def 4.10 with all r <= 1), with  *)
(* abs Rm below any b0 > 0 (large scalings flatten): b0 from P3_START makes *)
(* the dimensional existence time of PDE_CURVATURE_TIME reach T_1.          *)
(* ------------------------------------------------------------------------- *)

let P2_NORMALIZE_STATEMENT = new_definition
 `P2_NORMALIZE_STATEMENT (u:A->bool) <=>
    !top atlas g.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ riemannian_metric atlas g
        ==> !b0. &0 < b0
                 ==> ?q. &0 < q /\ rfs_normalized (top,atlas) (\x. q %% g x) /\
                         !x. x IN topspace top ==> mfd_rm_norm atlas (\x. q %% g x) x <= b0`;;

(* ------------------------------------------------------------------------- *)
(* The Part 2C vocabulary of these statements (also used by unit            *)
(* pc_p2c_views, which loads this unit through pc_p3_route): regions of a   *)
(* view carrying a Ricci flow, regular views (MT generalized Ricci flows as *)
(* the Ch 11 analysis uses them), geometric limits with explicit exhaustion *)
(* W and maps phi, kappa-solutions after MT Def 9.2 (smooth up to time 0).  *)
(* ------------------------------------------------------------------------- *)

let p2c_vfam = new_definition
 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
              (real->A->real^3^3)) (W:A->bool) (b:real) =
    \s. restrict_metric (rfs_vatlas V b) W
          (\x. if s = b then rfs_vmetric V b x
               else mfd_pullback_metric (rfs_vatlas V b) (rfs_vatlas V s) (\y. y)
                                        (rfs_vmetric V s) x)`;;

let p2c_vflow = new_definition
 `p2c_vflow (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
               (real->A->real^3^3)) (W:A->bool) (a:real) (b:real) <=>
    rfs_persists V W a b /\
    rfs_flow_upto (subtopology (rfs_vtop V b) W, restrict_atlas (rfs_vatlas V b) W) a b
                  (p2c_vfam V W b)`;;

let p2c_vflow_from = new_definition
 `p2c_vflow_from (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) (W:A->bool) (a:real) (b:real) <=>
    p2c_vflow V W a b /\ open_in (rfs_vtop V a) W /\
    ricci_flow_from (subtopology (rfs_vtop V b) W, restrict_atlas (rfs_vatlas V b) W) a b
                    (p2c_vfam V W b)`;;

(* Conjunct 5 makes the slice at the left end a of a region W open there     *)
(* smoothly compatible with the later slices (the identity is a diffeo from  *)
(* a to b); conjunct 4 covers only a < s.  Prop 5.14 needs it when J has     *)
(* least element 0.  Histories: P2CY_HIST_FROM_SMOOTH; flow views:           *)
(* P2CZ_FLOW_VIEW_FROM_SMOOTH (the body of p2cz_from_smooth of unit          *)
(* pc_p2c_vfrom is this conjunct).                                           *)

let p2c_regular_view = new_definition
 `p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)) <=>
    (!t. ~(topspace(rfs_vtop V t) = {})
         ==> hausdorff_space (rfs_vtop V t) /\
             smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
             riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t)) /\
    (!W a b. a < b /\ rfs_persists V W a b ==> p2c_vflow V W a b) /\
    (!W a b. a < b /\ open_in (rfs_vtop V a) W /\ rfs_persists V W a b
             ==> p2c_vflow_from V W a b) /\
    (!W a b s. a < s /\ s <= b /\ rfs_persists V W a b
               ==> mfd_diffeo (rfs_vtop V s) (rfs_vatlas V s) W
                              (rfs_vtop V b) (rfs_vatlas V b) W (\y:A. y) (\y. y)) /\
    (!W a b. a < b /\ open_in (rfs_vtop V a) W /\ rfs_persists V W a b
             ==> mfd_diffeo (rfs_vtop V a) (rfs_vatlas V a) W
                            (rfs_vtop V b) (rfs_vatlas V b) W (\y:A. y) (\y. y))`;;

let p2c_slice_limit_with = new_definition
 `p2c_slice_limit_with
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) (xl:B)
    (W:num->B->bool) (phi:num->B->A) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
    riemannian_metric atlas g /\ (!k. &0 < Q k) /\
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

let p2c_flow_limit_with = new_definition
 `p2c_flow_limit_with
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3))
    (x:num->A) (t:num->real) (Q:num->real) (J:real->bool)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
    (xl:B) (W:num->B->bool) (phi:num->B->A) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ xl IN topspace top /\
    (&0) IN J /\ (!k. &0 < Q k) /\
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

let p2c_kappa_sol = new_definition
 `p2c_kappa_sol (kappa:real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) <=>
    &0 < kappa /\ hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    connected_space top /\ ~(topspace top = {}) /\
    (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    (!t. t <= &0 ==> mfd_complete (top,atlas) (g t)) /\
    (!t x u v. t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional atlas (g t) x u v) /\
    (!t. t <= &0 ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g t) x <= K) /\
    (!t. t <= &0 ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g t) x) /\
    (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {t | t <= &0} g) kappa r0)`;;

(* The Part 2B vocabulary: kappa-solutions after MT Def 9.2 with abs Rm    *)
(* bounded on every compact time interval [a,0] (the notion of the         *)
(* corrected Thm 11.8 and Cor 9.95), and separation of the neck spheres in *)
(* every stage of a history (on the route from simply connected stages,    *)
(* P3_STRUCT_SPHERE_SEP of unit pc_p3_route).                              *)

let p2b_kappa_solution = new_definition
 `p2b_kappa_solution (kappa:real)
    (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) <=>
    p2c_kappa_sol kappa (top,atlas) g /\
    (!a. a <= &0
         ==> ?K. !t x. a <= t /\ t <= &0 /\ x IN topspace top
                       ==> mfd_rm_norm atlas (g t) x <= K)`;;

let p2b_hs_sep = new_definition
 `p2b_hs_sep (hs:(A)rfs_history) <=>
    !k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)`;;

(* ========================================================================= *)
(* PART 1 (MT Ch 1-5).                                                       *)
(* ========================================================================= *)

(* MT Thm 3.11, Prop 3.12, Prop 4.11 (curvature part) and Prop 4.12 are the  *)
(* PDE interface (unit pc_pde_iface):                                        *)
(* PDE_STE, PDE_UNIQUENESS, PDE_GLUE, PDE_CURVATURE_TIME (dimensional        *)
(* constants c, C instead of MT's 2^-4 and 2),                               *)
(* PDE_EXTENSION, PDE_MAXIMAL_FLOW, all at (:A) (:3); the route obligations  *)
(* use them (unit pc_p3_route).                                              *)

(* MT Thm 3.28 (Shi, local derivative estimates; p. 51; used p. 353, p. 371 *)
(* Claim 16.6 on strong necks, Lemma 11.21): a Ricci flow on (a,b] smooth up *)
(* to b on a possibly incomplete manifold, a ball at time b with compact     *)
(* closure on which abs Rm <= K over (a,b], b - a >= tau: then              *)
(* abs(nabla^l Rm) <= Cl on the half ball at time b.                          *)

let P2_THM_3_28_STATEMENT = new_definition
 `P2_THM_3_28_STATEMENT (u:A->bool) <=>
    !l K r tau. &0 < K /\ &0 < r /\ &0 < tau
      ==> ?Cl. !top atlas a b g x.
                 hausdorff_space top /\
                 rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
                 tau <= b - a /\ x IN topspace top /\
                 compact_in top (top closure_of mfd_ball (top,atlas) (g b) x r) /\
                 (!t y. a < t /\ t <= b /\ y IN mfd_ball (top,atlas) (g b) x r
                        ==> mfd_rm_norm atlas (g t) y <= K)
                 ==> !y. y IN mfd_ball (top,atlas) (g b) x (r / &2)
                         ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y) (g b))
                                               (SND(chart_at atlas y) y) <= Cl`;;

(* MT Thm 3.29 (Shi with initial bounds; p. 51; used p. 372-373 Lemma 16.8, *)
(* Cor 16.9 at the surgery caps): if moreover abs(nabla^j Rm) <= K at the    *)
(* initial time a for j <= l (the flow smooth from a), the bounds hold for   *)
(* all times in [a,b] on the half ball, with no blow-up at a.                *)

let P2_THM_3_29_STATEMENT = new_definition
 `P2_THM_3_29_STATEMENT (u:A->bool) <=>
    !l K r tau. &0 < K /\ &0 < r /\ &0 < tau
      ==> ?Cl. !top atlas a b g x.
                 hausdorff_space top /\
                 ricci_flow_from (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
                 b - a <= tau /\ x IN topspace top /\
                 compact_in top (top closure_of mfd_ball (top,atlas) (g a) x r) /\
                 (!t y. a <= t /\ t < b /\ y IN mfd_ball (top,atlas) (g a) x r
                        ==> mfd_rm_norm atlas (g t) y <= K) /\
                 (!j y. j <= l /\ y IN mfd_ball (top,atlas) (g a) x r
                        ==> lrm_deriv_norm2 j (metric_local atlas (chart_at atlas y) (g a))
                                              (SND(chart_at atlas y) y) <= K)
                 ==> !j t y. j <= l /\ a <= t /\ t < b /\
                             y IN mfd_ball (top,atlas) (g a) x (r / &2)
                             ==> lrm_deriv_norm2 j
                                   (metric_local atlas (chart_at atlas y) (g t))
                                   (SND(chart_at atlas y) y) <= Cl`;;

(* MT Lemma 3.14 (used p. 400 Claim 17.4, p. 405 Lemma 17.7, on the         *)
(* standard solution): under nonnegative Ricci curvature distances do not    *)
(* increase in time.                                                         *)

let P2_LEMMA_3_14_STATEMENT = new_definition
 `P2_LEMMA_3_14_STATEMENT (u:A->bool) <=>
    !top atlas a b g t1 t2 x y.
       hausdorff_space top /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       (!t z v. a < t /\ t < b /\ z IN topspace top
                ==> &0 <= mfd_ricci atlas (g t) z v v) /\
       a < t1 /\ t1 <= t2 /\ t2 < b /\ x IN topspace top /\ y IN topspace top
       ==> mfd_dist (top,atlas) (g t2) x y <= mfd_dist (top,atlas) (g t1) x y`;;

(* MT Prop 4.11, volume part (p. 67; used p. 353 Claim 15.1, pp. 363, 365): *)
(* a Ricci flow on a closed 3-manifold from a normalized metric with        *)
(* abs Rm <= K on [0,tau] is kappa0-noncollapsed there on scales <= 1,      *)
(* kappa0 depending on (K, tau).  (The existence time and curvature bound    *)
(* are PDE_CURVATURE_TIME.)                                                  *)

let P2_PROP_4_11_VOLUME_STATEMENT = new_definition
 `P2_PROP_4_11_VOLUME_STATEMENT (u:A->bool) <=>
    !K tau. &0 < K /\ &0 < tau
      ==> ?kappa0. &0 < kappa0 /\
            !top atlas b g.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               compact_space top /\ ricci_flow_from (top,atlas) (&0) b g /\ tau < b /\
               rfs_normalized (top,atlas) (g (&0)) /\
               (!t x. &0 <= t /\ t <= tau /\ x IN topspace top
                      ==> mfd_rm_norm atlas (g t) x <= K)
               ==> !t x r. &0 <= t /\ t <= tau /\ x IN topspace top /\ &0 < r /\ r <= &1
                           ==> ?v. mfd_has_volume (top,atlas) (g t)
                                     (mfd_ball (top,atlas) (g t) x r) v /\
                                   kappa0 * r pow 3 <= v`;;

(* MT Thm 4.23 as used on p. 393 (what is needed is that positive            *)
(* sectional curvature is preserved on a closed component, MT Cor 4.14 plus *)
(* the strong maximum principle of Cor 4.20; Thm 4.23 is about Ric).        *)

let P2_THM_4_23_STATEMENT = new_definition
 `P2_THM_4_23_STATEMENT (u:A->bool) <=>
    !top atlas a b g U.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       compact_space top /\ ricci_flow_from (top,atlas) a b g /\
       U IN connected_components_of top /\
       (!x u v. x IN U /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas (g a) x u v)
       ==> !t x u v. a <= t /\ t < b /\ x IN U /\ ~collinear {vec 0,u,v}
                     ==> &0 < mfd_sectional atlas (g t) x u v`;;

(* MT Thm 4.32 (p. 79; used p. 364 Lemma 15.11, the start): pinching toward *)
(* positive (MT Def 4.34 at time t, rfs_pinched_at) is preserved from any   *)
(* initial time a >= 0.                                                       *)

let P2_THM_4_32_STATEMENT = new_definition
 `P2_THM_4_32_STATEMENT (u:A->bool) <=>
    !top atlas a b g.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       compact_space top /\ &0 <= a /\ ricci_flow_from (top,atlas) a b g /\
       (!x. x IN topspace top ==> rfs_pinched_at atlas (g a) a x)
       ==> !t x. a <= t /\ t < b /\ x IN topspace top
                 ==> rfs_pinched_at atlas (g t) t x`;;

(* Volume growth (MT p. 410, no number: dVol/dt = - integral of R): if      *)
(* R >= -K on [t1,t2] then Vol(t2) <= exp(K (t2 - t1)) Vol(t1).  Used by     *)
(* Lemma 17.12 with K = 6 (pinching).                                         *)

let P2_VOLUME_GROWTH_STATEMENT = new_definition
 `P2_VOLUME_GROWTH_STATEMENT (u:A->bool) <=>
    !top atlas a b g K t1 t2 v1 v2.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       compact_space top /\ ricci_flow_from (top,atlas) a b g /\
       a <= t1 /\ t1 <= t2 /\ t2 < b /\
       (!t x. t1 <= t /\ t <= t2 /\ x IN topspace top ==> --K <= mfd_scalar atlas (g t) x) /\
       mfd_has_volume (top,atlas) (g t1) (topspace top) v1 /\
       mfd_has_volume (top,atlas) (g t2) (topspace top) v2
       ==> v2 <= exp(K * (t2 - t1)) * v1`;;

(* MT Prop 2.19 (p. 31; used p. 407 in Prop 17.1, constants p. 354): for eps *)
(* small a complete connected positively curved 3-manifold has no eps-necks *)
(* of arbitrarily small scale.  Corrected: connectedness is assumed (a      *)
(* disjoint union of shrinking ellipsoids is a counterexample).  Body:      *)
(* P2B_PROP_2_19_FIX_STATEMENT.  On p. 407 and p. 278 MT applies it to      *)
(* limits with only Rm >= 0; the route form P2_PROP_2_19_SEP below covers   *)
(* that case: sec >= 0 and separating neck spheres (Part 2B, by Toponogov,  *)
(* without the strong maximum principle).                                   *)

let P2_PROP_2_19_STATEMENT = new_definition
 `P2_PROP_2_19_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !eps top atlas g.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ connected_space top /\
         smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
         (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 < mfd_sectional atlas g x u v)
         ==> ?B. !x e. rfs_neck (top,atlas) g eps x e ==> mfd_scalar atlas g x <= B`;;

(* The route form of MT Prop 2.19 (Part 2B, used p. 407 on blow-up limits, *)
(* which are separating by P2_SEP_LIMIT): Body: P2B_PROP_2_19_SEP_STATEMENT. *)

let P2_PROP_2_19_SEP_STATEMENT = new_definition
 `P2_PROP_2_19_SEP_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !eps top atlas g.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\ connected_space top /\
         smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
         apx_sphere_sep top atlas /\
         (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas g x u v)
         ==> ?B. !x e. rfs_neck (top,atlas) g eps x e ==> mfd_scalar atlas g x <= B`;;

(* MT Thm 5.11 (p. 89; used p. 407): geometric limits of rescaled time      *)
(* slices of based histories with curvature bounds on backward parabolic    *)
(* balls of every radius and a volume lower bound at the base.  The limit   *)
(* lives on the carrier type B (it must carry every complete 3-manifold,    *)
(* e.g. real^7).                                                            *)

let P2_THM_5_11_STATEMENT = new_definition
 `P2_THM_5_11_STATEMENT (u:A->bool) (w:B->bool) <=>
    !hs x t Q.
       (!n. rfs_history_ok (hs n:(A)rfs_history) /\ &0 < Q n /\
            x n IN topspace(rfs_top_at (hs n) (t n))) /\
       (!A. &0 < A
            ==> ?CA dA N. &0 < dA /\
                  !n. N <= n
                      ==> rfs_persists (rfs_view (hs n))
                            (rfs_vball (rfs_view (hs n)) (t n) (x n) (A * inv(sqrt(Q n))))
                            (t n - dA * inv(Q n)) (t n) /\
                          !s y. t n - dA * inv(Q n) < s /\ s <= t n /\
                                y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                       (A * inv(sqrt(Q n)))
                                ==> p3_vrm (rfs_view (hs n)) s y <= CA * Q n) /\
       (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
          !n. N <= n
              ==> ?v. mfd_has_volume (rfs_top_at (hs n) (t n),rfs_atlas_at (hs n) (t n))
                        (rfs_metric_at (hs n) (t n))
                        (rfs_vball (rfs_view (hs n)) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                      kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
       ==> ?sub (top:B topology) atlas g xl.
              p3_subseq sub /\
              p3_slice_limit (\n. rfs_view (hs (sub n))) (x o sub) (t o sub) (Q o sub)
                             (top,atlas) g xl`;;

(* MT Prop 5.14 / Thm 5.15 (Hamilton compactness; used without number in     *)
(* Lemma 16.8 and Cor 16.9 for the forward flows near surgery caps, and      *)
(* inside Thm 11.8): based histories, rescaled by Q n at times t n, with     *)
(* curvature bounds C(A,I) on B(x n, t n, A Q n^(-1/2)) over the rescaled    *)
(* compact time intervals I in the interval J, persisting there, and a       *)
(* volume lower bound at the base: a subsequence converges to a Ricci flow   *)
(* on J.  Corrected: if J has a least element a0, the rescaled derivative    *)
(* bounds at time a0 are assumed; the slice at 0 is complete, and so are the *)
(* slices of [a,b] when the curvature bound there is uniform in A.  Body:    *)
(* P2C_THM_5_15_STATEMENT.  A deliberate restriction: the least element of   *)
(* J, if any, is 0.  A least element a0 < 0 would need the flow extended     *)
(* down to a0 by a Shi estimate from the bottom; a consumer with a closed    *)
(* bottom shrinks J to an interval without least element.                    *)

let P2_THM_5_15_STATEMENT = new_definition
 `P2_THM_5_15_STATEMENT (u:A->bool) (w:B->bool) <=>
    !hs x t Q J.
       is_realinterval J /\ (&0) IN J /\
       (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
       (!n. rfs_history_ok (hs n:(A)rfs_history) /\ &0 < Q n /\
            x n IN topspace(rfs_top_at (hs n) (t n))) /\
       (!A a b. &0 < A /\ real_interval[a,b] SUBSET J
                ==> ?CA N. !n. N <= n
                        ==> (!s. a <= s /\ s <= b
                                 ==> rfs_vball (rfs_view (hs n)) (t n) (x n)
                                       (A * inv(sqrt(Q n))) SUBSET
                                     topspace(rfs_top_at (hs n) (t n + s / Q n))) /\
                            rfs_persists (rfs_view (hs n))
                              (rfs_vball (rfs_view (hs n)) (t n) (x n) (A * inv(sqrt(Q n))))
                              (t n + a / Q n) (t n + b / Q n) /\
                            !s y. a <= s /\ s <= b /\
                                  y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                         (A * inv(sqrt(Q n)))
                                  ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <= CA * Q n) /\
       (!a0 A l. a0 IN J /\ (!s. s IN J ==> a0 <= s) /\ &0 < A
                 ==> ?CAl N. !n y. N <= n /\
                                   y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                          (A * inv(sqrt(Q n)))
                                   ==> p3_vderiv2 (rfs_view (hs n)) l (t n + a0 / Q n) y <=
                                       CAl * Q n pow (l + 2)) /\
       (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
          !n. N <= n
              ==> ?v. mfd_has_volume (rfs_top_at (hs n) (t n),rfs_atlas_at (hs n) (t n))
                        (rfs_metric_at (hs n) (t n))
                        (rfs_vball (rfs_view (hs n)) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                      kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
       ==> ?sub (top:B topology) atlas g xl.
              p3_subseq sub /\
              p3_flow_limit_on (\n. rfs_view (hs (sub n))) (x o sub) (t o sub) (Q o sub) J
                               (top,atlas) g xl /\
              (!s. s IN J ==> riemannian_metric atlas (g s)) /\
              mfd_complete (top,atlas) (g (&0)) /\
              (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
              (!a b CI. a <= &0 /\ &0 <= b /\ real_interval[a,b] SUBSET J /\
                        (!A. &0 < A
                             ==> ?N. !n s y. N <= n /\ a <= s /\ s <= b /\
                                             y IN rfs_vball (rfs_view (hs n)) (t n) (x n)
                                                    (A * inv(sqrt(Q n)))
                                             ==> p3_vrm (rfs_view (hs n)) (t n + s / Q n) y <=
                                                 CI * Q n)
                        ==> !s. a <= s /\ s <= b ==> mfd_complete (top,atlas) (g s))`;;

(* MT Prop 5.14 over a given time-0 limit (the Part 2C statement            *)
(* P2C_PROP_5_14; used in Lemma 16.8 for the                                *)
(* forward flows near surgery caps): regular views with a time-0 limit      *)
(* (W, phi, g0) and curvature bounds on the images of W m over the compact *)
(* intervals of J (least element 0 if any): a subsequence converges to a   *)
(* Ricci flow on J with the same W, maps phi and initial slice g0.  Its    *)
(* views are regular for histories by P2C_HISTORY_REGULAR (Part 2C derives *)
(* it from P3_LEMMA_14_11).  The last conjunct gives                       *)
(* smoothness from time 0 (ricci_flow_from), needed when 0 is the least     *)
(* element of J (Lemma 16.8: the limit is a partial standard flow).          *)

let P2C_PROP_5_14_STATEMENT = new_definition
 `P2C_PROP_5_14_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q J top atlas g0 xl W phi.
       is_realinterval J /\ (&0) IN J /\
       (!a0. a0 IN J /\ (!s. s IN J ==> a0 <= s) ==> a0 = &0) /\
       (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3))) /\
       p2c_slice_limit_with V x t Q (top:B topology,atlas) g0 xl W phi /\
       (!m a b. real_interval[a,b] SUBSET J
                ==> ?CM N. !n. N <= n
                         ==> (!s. a <= s /\ s <= b
                                  ==> IMAGE (phi n) (W m) SUBSET
                                      topspace(rfs_vtop (V n) (t n + s / Q n))) /\
                             rfs_persists (V n) (IMAGE (phi n) (W m))
                                          (t n + a / Q n) (t n + b / Q n) /\
                             !s y. a <= s /\ s <= b /\ y IN IMAGE (phi n) (W m)
                                   ==> p3_vrm (V n) (t n + s / Q n) y <= CM * Q n)
       ==> ?sub g. p3_subseq sub /\ g (&0) = g0 /\
                   p2c_flow_limit_with (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) J
                                       (top,atlas) g xl W (phi o sub) /\
                   (!s. s IN J ==> riemannian_metric atlas (g s)) /\
                   (!a b. a < b /\ real_interval[a,b] SUBSET J ==> ricci_flow_on (top,atlas) a b g) /\
                   (!b. &0 < b /\ real_interval[&0,b] SUBSET J
                        ==> ricci_flow_from (top,atlas) (&0) b g)`;;

let P2C_HISTORY_REGULAR_STATEMENT = new_definition
 `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool) <=>
    !hs:(A)rfs_history. rfs_history_ok hs ==> p2c_regular_view (rfs_view hs)`;;

(* Views of ordinary Ricci flows smooth from their initial time are regular *)
(* (P2C_FLOW_VIEW_REGULAR, proved in pc_p2c_fview; the source of the neck   *)
(* transfer from the standard solution in Lemma 17.7 is such a view).       *)

let P2C_FLOW_VIEW_REGULAR_STATEMENT = new_definition
 `P2C_FLOW_VIEW_REGULAR_STATEMENT (u:A->bool) <=>
    !top atlas a b g.
       hausdorff_space (top:A topology) /\
       ricci_flow_from (top,atlas:((A->bool)#(A->real^3))->bool) a b g
       ==> p2c_regular_view (rfs_flow_view (top,atlas) {s | a <= s /\ s < b} g)`;;

(* ========================================================================= *)
(* PART 2 (MT Ch 6-12).                                                      *)
(* ========================================================================= *)

(* MT Thm 8.1 with Prop 6.56 and Cor 6.67 (pp. 169, 147, 151; used p. 394,  *)
(* end of the proof of Prop 16.1), in the form used: x at time tt with an   *)
(* existing backward parabolic neighbourhood P(x,tt,r,-r^2) on which abs Rm *)
(* <= r^-2 (half-open); an open B in the slice at tt - tau0 of              *)
(* volume >= V0 all of whose points are reached by minimizing L-geodesics   *)
(* from x of reduced length <= l0 lying in a compact subset K of the smooth *)
(* part (MT Prop 16.21): then Vol B(x,tt,r) >= kappa r^3, kappa depending   *)
(* on (taub, l0, V0).  Cor 6.67 turns B into the full-measure image of the  *)
(* injectivity domain needed by Thm 8.1 (4)-(5).                             *)

let P2_THM_8_1_STATEMENT = new_definition
 `P2_THM_8_1_STATEMENT (u:A->bool) <=>
    !taub l0 V0. &0 < taub /\ &0 < V0
      ==> ?kappa. &0 < kappa /\
            !(hs:(A)rfs_history) x tt r tau0 B K.
               rfs_history_ok hs /\ &0 < tau0 /\ tau0 <= taub /\ tau0 < tt /\
               &0 < r /\ r pow 2 <= tau0 /\ x IN topspace(rfs_top_at hs tt) /\
               rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
               (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
                      ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
               open_in (rfs_top_at hs (tt - tau0)) B /\
               (?v. mfd_has_volume (rfs_top_at hs (tt - tau0),rfs_atlas_at hs (tt - tau0))
                                   (rfs_metric_at hs (tt - tau0)) B v /\ V0 <= v) /\
               p3_st_compact hs K /\
               (!q. q IN B
                    ==> ?gamma. rfs_min_Lgeod hs tt x tau0 gamma /\ gamma tau0 = q /\
                                rfs_lx hs tt x tau0 q <= l0 /\
                                !tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K (tt - tau))
               ==> ?v. mfd_has_volume (rfs_top_at hs tt,rfs_atlas_at hs tt) (rfs_metric_at hs tt)
                                      (rfs_vball (rfs_view hs) tt x r) v /\
                       kappa * r pow 3 <= v`;;

(* MT Lemma 7.2 (p. 133; used p. 387 in Prop 16.21, as in Lemma 7.2): the    *)
(* direct method in a compact subset K of the smooth part: admissible curves *)
(* from x with L <= Lb staying in K subconverge uniformly to a curve gamma   *)
(* from x in a compact subset K' of the smooth part, with L lower            *)
(* semicontinuous in competitor form (for every eta an admissible curve in   *)
(* K' with the same endpoint and L at most the L of the curves plus eta); if *)
(* they all end at q and their L tends to the infimum, gamma is a minimizing *)
(* L-geodesic.  Corrected: the uniform limit need not be C^1, so it is not   *)
(* asserted to be admissible.  Body: P2A_LEMMA_7_2_FIXED_STATEMENT.  The     *)
(* minimizer clause also gives gamma tau0 = q (needed by Cor 16.24;          *)
(* P2AJ_MB_7_2_C has it).                                                    *)

let P2_LEMMA_7_2_STATEMENT = new_definition
 `P2_LEMMA_7_2_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) x tt tau0 K gs Lb.
       rfs_history_ok hs /\ &0 < tau0 /\ tau0 < tt /\ p3_st_compact hs K /\
       (!n. rfs_L_adm hs tt x tau0 (gs n) /\ rfs_L_length hs tt (gs n) tau0 <= Lb /\
            !tau. &0 < tau /\ tau <= tau0 ==> gs n tau IN K (tt - tau))
       ==> ?sub gamma K'.
              p3_subseq sub /\ p3_st_compact hs K' /\ gamma (&0) = x /\
              (!tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K' (tt - tau)) /\
              (!eta. &0 < eta
                     ==> (?gamma'. rfs_L_adm hs tt x tau0 gamma' /\ gamma' tau0 = gamma tau0 /\
                                   (!tau. &0 < tau /\ tau <= tau0
                                          ==> gamma' tau IN K' (tt - tau)) /\
                                   ?N. !n. N <= n
                                       ==> rfs_L_length hs tt gamma' tau0 <=
                                           rfs_L_length hs tt (gs (sub n)) tau0 + eta) /\
                         (?N. !n. N <= n
                              ==> !tau. &0 <= tau /\ tau <= tau0
                                        ==> mfd_dist (rfs_top_at hs (tt - tau),
                                                      rfs_atlas_at hs (tt - tau))
                                                     (rfs_metric_at hs (tt - tau))
                                                     (gs (sub n) tau) (gamma tau) < eta)) /\
              !q. (!n. gs n tau0 = q) /\
                  (!eta. &0 < eta
                         ==> ?N. !n. N <= n
                                 ==> rfs_L_length hs tt (gs n) tau0 <=
                                     rfs_Lx hs tt x tau0 q + eta)
                  ==> rfs_min_Lgeod hs tt x tau0 gamma /\ gamma tau0 = q`;;

(* MT Cor 7.12 (p. 156; used p. 390, Lemma 16.26): an open U in the smooth  *)
(* part of times [a,tt) with (1) minimizing L-geodesics from x to all its   *)
(* points, (2) containing the lower part of a backward parabolic            *)
(* neighbourhood of x, (3) compact non-empty sets of slice minimizers over  *)
(* compact time intervals,                                                   *)
(* (4) lower semicontinuity in time of the slice minimum of l_x (added:     *)
(* without it the original is unprovable; Part 3 proves it for              *)
(* its U as in MT Claim 16.25): then min of l_x on each slice is <= 3/2.    *)
(* Body: P2A_COR_7_12_FIXED_STATEMENT.  In (2) only x IN U s is required    *)
(* for tt - dt < s < tt (the parabolic neighbourhood still exists); MT's    *)
(* proof uses only the vertical path at x.  This form implies MT's.         *)

let P2_COR_7_12_STATEMENT = new_definition
 `P2_COR_7_12_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) x tt a U r dt.
       rfs_history_ok hs /\ a < tt /\ x IN topspace(rfs_top_at hs tt) /\
       p3_st_open hs U a tt /\
       (!t y. y IN U t ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\
                                   gamma (tt - t) = y) /\
       &0 < r /\ &0 < dt /\ rfs_parabolic_exists (rfs_view hs) tt x r dt /\
       (!s. tt - dt < s /\ s < tt /\ a <= s ==> x IN U s) /\
       (!a' b'. a <= a' /\ a' <= b' /\ b' < tt
                ==> p3_st_compact hs (\t. if a' <= t /\ t <= b' then p3_Lmin_set hs tt x U t
                                          else {}) /\
                    !t. a' <= t /\ t <= b' ==> ~(p3_Lmin_set hs tt x U t = {})) /\
       (!t e. a <= t /\ t < tt /\ &0 < e
              ==> ?d. &0 < d /\
                      !t' y'. a <= t' /\ t' < tt /\ abs(t' - t) < d /\ y' IN U t'
                              ==> ?y. y IN U t /\
                                      rfs_lx hs tt x (tt - t) y <=
                                      rfs_lx hs tt x (tt - t') y' + e)
       ==> !t. a <= t /\ t < tt ==> ?y. y IN U t /\ rfs_lx hs tt x (tt - t) y <= &3 / &2`;;

(* MT Prop 9.79 (p. 233; used pp. 396-397, 401, 405, 407): stability of     *)
(* canonical neighbourhoods.  (a) Slice form (parts 1 and 3): a             *)
(* (C,eps)-canonical neighbourhood U of x transfers along a map psi whose   *)
(* pullback metric is delta-close on U at the scale R(x), with constants    *)
(* (C',eps') (components must map onto components).  Corrected: a           *)
(* universal factor K, 2C <= C', K eps <= eps' <= eps0 (re-centring the end *)
(* neck of a cap costs a factor K), a complete target, and a parameter Kr   *)
(* with the scale-invariant C^2 curvature bound lrm_deriv_norm2 l <= Kr     *)
(* (l <= 2) of the normalized metric R(x) g on U (delta may depend on Kr;   *)
(* the cap clauses do not control the curvature derivatives).  Body:        *)
(* P2B_PROP_9_79_SLICE_FIX_STATEMENT of unit pc_p2b_defs.                   *)

let P2_PROP_9_79_SLICE_STATEMENT = new_definition
 `P2_PROP_9_79_SLICE_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
               rfs_canonical_nbhd (top,atlas) g C eps x U /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local atlas (chart_at atlas y)
                               (\z. mfd_scalar atlas g x %% g z))
                            (SND(chart_at atlas y) y) <= Kr) /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               (U IN connected_components_of top
                ==> IMAGE psi U IN connected_components_of top') /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U'. U' SUBSET IMAGE psi U /\
                        rfs_canonical_nbhd (top',atlas') g' C' eps' (psi x) U'`;;

(* (b) Neck form (parts 2 and 4): an evolving eps-neck at (x,t) of          *)
(* normalized length a > 1 transfers to a strong eps'-neck at (psi x, t')   *)
(* in any view delta-close on the neck over the normalized times (-a,0]    *)
(* with smooth slices.  Corrected: eps < eps' (the uniform same-eps form is *)
(* false), the slices of V' are smooth manifolds, the source view is regular *)
(* (p2c_regular_view: the closeness at earlier times is read in the slice   *)
(* atlases, where the neck chart must be smooth) and the target slices      *)
(* carry Riemannian metrics.  Body: P2B_PROP_9_79_NECK_FIX_STATEMENT of     *)
(* unit pc_p2b_defs.                                                        *)

let P2_PROP_9_79_NECK_STATEMENT = new_definition
 `P2_PROP_9_79_NECK_STATEMENT (u:A->bool) (w:B->bool) <=>
    !eps eps' a. &0 < eps /\ eps < eps' /\ eps' < &1 / &4 /\ &1 < a
      ==> ?delta. &0 < delta /\
            !V x t e V' t' Q' psi.
               p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) /\
               rfs_evolving_neck V eps x t a e /\
               (!s. --a < s /\ s <= &0
                    ==> smooth_manifold_atlas (rfs_vtop V' (t' + s / Q'))
                                              (rfs_vatlas V' (t' + s / Q')) /\
                        riemannian_metric (rfs_vatlas V' (t' + s / Q'))
                                          (rfs_vmetric V' (t' + s / Q'))) /\
               p3_view_close V t (rfs_vscalar V t x) (IMAGE e (rfs_neck_dom eps))
                 (V':(real->B topology)#(real->((B->bool)#(B->real^3))->bool)#
                     (real->B->real^3^3)) t' Q' psi {s | --a < s /\ s <= &0} delta
               ==> ?e'. rfs_strong_neck V' eps' (psi x) t' e'`;;

(* (c) Open form (MT Prop 9.79(1) as used on p. 396, in Lemma 17.2, and in   *)
(* Cor 9.95): the same set U is a (C,eps)-canonical neighbourhood of psi x   *)
(* for every complete target metric close enough (closeness depending on U   *)
(* and g).  Body: P2B_PROP_9_79_OPEN_STATEMENT.                              *)

let P2_PROP_9_79_OPEN_STATEMENT = new_definition
 `P2_PROP_9_79_OPEN_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
    !C eps top atlas g x U.
       &1 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\
       rfs_canonical_nbhd (top,atlas) g C eps x U /\
       compact_in top (top closure_of U)
       ==> ?delta. &0 < delta /\
             !top' atlas' g' psi psi'.
                hausdorff_space top' /\
                smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
                mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
                (U IN connected_components_of top
                 ==> IMAGE psi U IN connected_components_of top') /\
                rfs_mclose (rfs_kreg delta) delta atlas U
                  (\y. mfd_scalar atlas g x %% g y)
                  (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
                ==> rfs_canonical_nbhd (top',atlas') g' C eps (psi x) (IMAGE psi U)`;;

(* MT Cor 9.95 with Cor 9.94 (p. 243; used p. 403 in Prop 17.1): there is    *)
(* eps' such that for eps <= eps' there is C(eps) with: if based histories   *)
(* with orientable stages (so no embedded RP^2 with trivial normal bundle)   *)
(* have an ancient rescaled limit flow that is a kappa-solution, then for n  *)
(* large x n has a strong (C,eps)-canonical neighbourhood, for every C >=    *)
(* C(eps).  Corrected: the kappa-solution notion is p2b_kappa_solution (the  *)
(* notion of the corrected Thm 11.8) and the stages separate along neck      *)
(* spheres (p2b_hs_sep).  Body: P2B_COR_9_95_FIX_STATEMENT.  The             *)
(* neighbourhood is a canonv one (p3_canonv_at: KL's volume clause on        *)
(* C-components, constant uniform in kappa through kappa0 of P2B_PROP_9_58). *)

let P2_COR_9_95_STATEMENT = new_definition
 `P2_COR_9_95_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?epsp. &0 < epsp /\
      !eps. &0 < eps /\ eps <= epsp
        ==> ?C95. &1 < C95 /\
              !C hs x t Q top atlas g xl kappa.
                 C95 <= C /\
                 (!n. rfs_history_ok (hs n:(A)rfs_history) /\ p2b_hs_sep (hs n) /\
                      x n IN topspace(rfs_top_at (hs n) (t n)) /\
                      !k. k <= hs_count (hs n)
                          ==> mfd_orientable (hs_top (hs n) k) (hs_atlas (hs n) k)) /\
                 (!Tl. &0 < Tl
                       ==> p3_flow_limit (\n. rfs_view (hs n)) x t Q
                                         (top:B topology,atlas) g xl Tl) /\
                 p2b_kappa_solution kappa (top,atlas) g
                 ==> ?N. !n. N <= n ==> p3_canonv_at (rfs_view (hs n)) C eps (x n) (t n)`;;

(* MT Thm 10.2 (p. 245; used p. 406 Claim 17.9, constants p. 354): bounded  *)
(* curvature at bounded distance; no noncollapsing assumed.  Corrected:     *)
(* the stages separate along neck spheres                                   *)
(* (p2b_hs_sep; the proof uses the separating Appendix).  Body:             *)
(* P2B_THM_10_2_FIX_STATEMENT.                                               *)

let P2_THM_10_2_STATEMENT = new_definition
 `P2_THM_10_2_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps C A. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A
        ==> ?D0 D. &0 < D0 /\ &0 < D /\
              !(hs:(A)rfs_history) x t.
                 rfs_history_ok hs /\ p2b_hs_sep hs /\ rfs_pinched (rfs_view hs) /\
                 &0 <= t /\ x IN topspace(rfs_top_at hs t) /\
                 (!y s. s <= t /\ y IN topspace(rfs_top_at hs s) /\
                        &4 * rfs_vscalar (rfs_view hs) t x <= rfs_vscalar (rfs_view hs) s y
                        ==> p3_canon_at (rfs_view hs) C eps y s) /\
                 D0 <= rfs_vscalar (rfs_view hs) t x
                 ==> !y. y IN rfs_vball (rfs_view hs) t x
                                (A * inv(sqrt(rfs_vscalar (rfs_view hs) t x)))
                         ==> rfs_vscalar (rfs_view hs) t y <= D * rfs_vscalar (rfs_view hs) t x`;;

(* MT Lemma 11.2 (p. 268; used pp. 372-373, 392, 406-408): curvature control *)
(* on short parabolic regions from the canonical neighbourhood assumption   *)
(* above r0^-2 on the time window, for a ball persisting over it.           *)
(* Corrected: eps <= eps0 and C >= 2 (on eps-necks the                      *)
(* derivative bounds come only from closeness), and R(z) is replaced by    *)
(* max 0 R(z).  Body: P2C_LEMMA_11_2_STATEMENT.                              *)

let P2_LEMMA_11_2_STATEMENT = new_definition
 `P2_LEMMA_11_2_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !(hs:(A)rfs_history) C eps r0 z t0 t' r'.
         rfs_history_ok hs /\ &2 <= C /\ &0 < eps /\ eps <= eps0 /\ &0 < r0 /\
         (!x t. min t0 t' <= t /\ t <= max t0 t' /\ x IN topspace(rfs_top_at hs t) /\
                inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                ==> p3_canon_at (rfs_view hs) C eps x t) /\
         z IN topspace(rfs_top_at hs t0) /\ &0 < r' /\
         r' <= inv(&2 * C * sqrt(max (rfs_vscalar (rfs_view hs) t0 z) (inv(r0 pow 2)))) /\
         abs(t' - t0) <=
         inv(&16 * C * (max (&0) (rfs_vscalar (rfs_view hs) t0 z) + inv(r0 pow 2))) /\
         rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 z r') (min t0 t') (max t0 t')
         ==> !s y. min t0 t' < s /\ s <= max t0 t' /\ y IN rfs_vball (rfs_view hs) t0 z r'
                   ==> rfs_vscalar (rfs_view hs) s y <=
                       &2 * (max (&0) (rfs_vscalar (rfs_view hs) t0 z) + inv(r0 pow 2))`;;

(* MT Thm 11.8 (p. 272; used pp. 403, 408): blow-up limits of based          *)
(* histories satisfying Thm 11.1 (1)-(5) whose balls persist backward for    *)
(* every rescaled time Tb < T0, kappa-noncollapsed there (without the        *)
(* exemption of p. 360, which Part 3 supplies): a complete limit flow on     *)
(* (-T0,0] with Rm >= 0 and curvature locally bounded in time; for every T0  *)
(* (ancient case) the limit is a kappa-solution.  eps <= eps0 lets it be     *)
(* applied with (2C,2eps).  Corrected: the kappa-solution is in the sense of *)
(* MT Def 9.2, with abs Rm bounded on compact time intervals                 *)
(* (p2b_kappa_solution; the limit exists only on (-inf,0]), and the stages   *)
(* separate along neck spheres (apx_sphere_sep; on the route from p3_struct  *)
(* by RFS_HISTORY_SC and SMT_SC_SPHERE_SEP).  Body: P2C_THM_11_8_STATEMENT.  *)
(* With MT Cor 11.16, abs Rm is bounded on B(x_inf,0,A) x (-T0,0] for every  *)
(* A (the T' < infinity step of Prop 17.1, p. 408).                          *)

let P2_THM_11_8_STATEMENT = new_definition
 `P2_THM_11_8_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps kappa r0 mu (hs:num->(A)rfs_history) x t.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         p3_blowup_seq (C,eps,kappa,r0,mu) hs x t /\
         (!n k. k <= hs_count (hs n) ==> apx_sphere_sep (hs_top (hs n) k) (hs_atlas (hs n) k))
         ==> (!T0. &0 < T0 /\ (!Tb. &0 < Tb /\ Tb < T0 ==> p3_blowup_back (kappa,r0) hs x t Tb)
                   ==> ?sub (top:B topology) atlas g xl.
                          p3_subseq sub /\
                          p3_flow_limit (\n. rfs_view (hs (sub n))) (x o sub) (t o sub)
                            (\n. rfs_vscalar (rfs_view (hs (sub n))) (t (sub n)) (x (sub n)))
                            (top,atlas) g xl T0 /\
                          (!s. --T0 < s /\ s <= &0
                               ==> mfd_complete (top,atlas) (g s) /\
                                   !y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                                           ==> &0 <= mfd_sectional atlas (g s) y u v) /\
                          (!a. --T0 < a
                               ==> ?K. !s y. a <= s /\ s <= &0 /\ y IN topspace top
                                             ==> mfd_rm_norm atlas (g s) y <= K) /\
                          (!A. ?K. !s y. --T0 < s /\ s <= &0 /\
                                         y IN mfd_ball (top,atlas) (g (&0)) xl A
                                         ==> mfd_rm_norm atlas (g s) y <= K)) /\
             ((!Tb. &0 < Tb ==> p3_blowup_back (kappa,r0) hs x t Tb)
              ==> ?sub (top:B topology) atlas g xl.
                     p3_subseq sub /\
                     (!Tl. &0 < Tl
                           ==> p3_flow_limit (\n. rfs_view (hs (sub n))) (x o sub) (t o sub)
                                 (\n. rfs_vscalar (rfs_view (hs (sub n))) (t (sub n)) (x (sub n)))
                                 (top,atlas) g xl Tl) /\
                     p2b_kappa_solution kappa (top,atlas) g)`;;

(* Separation passes to geometric limits of histories whose stages separate *)
(* (Part 2B, elementary: a path joining the two sides of a neck sphere in   *)
(* the limit lies in some W k and maps into a stage); used with             *)
(* P2_PROP_2_19_SEP on p. 407.  Body: P2B_SEP_LIMIT_STATEMENT.               *)

let P2_SEP_LIMIT_STATEMENT = new_definition
 `P2_SEP_LIMIT_STATEMENT (u:A->bool) (w:B->bool) <=>
    !hs x t Q top atlas g xl Tl.
       (!n. rfs_history_ok (hs n:(A)rfs_history) /\ p2b_hs_sep (hs n) /\
            x n IN topspace(rfs_top_at (hs n) (t n))) /\
       p3_flow_limit (\n. rfs_view (hs n)) x t Q (top:B topology,atlas) g xl Tl
       ==> apx_sphere_sep top atlas`;;

(* MT Lemma 11.23 with Claim 11.24 (pp. 281-282; used p. 403, Claim 17.6):   *)
(* if x has strong (C,eps)-canonical neighbourhoods at all earlier times     *)
(* near t, all inside a compact set K of the slice at t contained in a set W *)
(* persisting over (t - eta, t], then (x,t) has a strong (2C,2eps)-          *)
(* canonical neighbourhood.  Corrected: MT's form (smooth point, flow line)  *)
(* is false at event times next to new caps.  Body:                          *)
(* P2C_LEMMA_11_23_STATEMENT.                                                *)

let P2_LEMMA_11_23_STATEMENT = new_definition
 `P2_LEMMA_11_23_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps (hs:(A)rfs_history) x t eta W K.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < eta /\
         x IN K /\ compact_in (rfs_top_at hs t) K /\ K SUBSET W /\
         rfs_persists (rfs_view hs) W (t - eta) t /\
         (!s. t - eta < s /\ s < t
              ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x s U /\ U SUBSET K)
         ==> p3_canon_at (rfs_view hs) (&2 * C) (&2 * eps) x t`;;

(* Canonical neighbourhoods with separate neck and cap constants.            *)
(* p3_canon_typed V C en ec x t: (x,t) is the centre of a strong en-neck, or *)
(* lies in the core of a (C,ec)-cap, or in a C-component, or in an ec-round  *)
(* component (the alternatives of rfs_strong_canonical; with en = ec this is *)
(* p3_canon_at).  MT Thm 11.19 (5) in the maximal extension gives 2 eps      *)
(* necks and Kc eps caps (the limits of caps are re-centred).                *)

let p3_canon_typed = new_definition
 `p3_canon_typed (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)) (C:real) (en:real) (ec:real) (x:A) (t:real) <=>
    (?e. rfs_strong_neck V en x t e) \/
    (?U Y. rfs_cap (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C ec U Y /\ x IN Y) \/
    (?U. x IN U /\ rfs_c_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) C U) \/
    (?U. x IN U /\ rfs_round_component (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t) ec U)`;;

(* MT Thm 11.19 (pp. 279-280, items (1) and (5); used p. 361 Sec 15.4 and    *)
(* p. 364 Lemma 15.11): at the horizon T of a history satisfying             *)
(* MT Assumptions 11.18 with r0 (pinching, strong (C,eps)-canonical          *)
(* neighbourhoods above r0^-2 before T), Omega (liminf R finite) is open,    *)
(* the slab metrics converge smoothly on compact subsets of Omega to a limit *)
(* gl, and points of Omega with R(gl) > r0^-2 have strong                    *)
(* (2C,2eps)-canonical neighbourhoods in the maximal extension.  As in       *)
(* P2C_THM_11_19_STATEMENT, the canonical clause holds for every limit       *)
(* metric gl and is typed: 2eps necks and (2C, Kc eps) caps and round        *)
(* components, for one Kc >= 2.                                              *)

let P2_THM_11_19_STATEMENT = new_definition
 `P2_THM_11_19_STATEMENT (u:A->bool) <=>
    ?Kc eps0. &2 <= Kc /\ &0 < eps0 /\
      !C eps (hs:(A)rfs_history) r0.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
         rfs_pinched (rfs_view hs) /\
         (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                ==> p3_canon_at (rfs_view hs) C eps x t)
         ==> open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
             (?gl. rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                     (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl) /\
             !gl. rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                    (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
                  ==> !x. x IN p3_omega hs /\
                          inv(r0 pow 2) < mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                          ==> p3_canon_typed (p3_maxext hs (p3_omega hs) gl) (&2 * C)
                                             (&2 * eps) (Kc * eps) x (rfs_horizon hs)`;;

(* MT Lemma 11.30 (p. 284; used p. 361): for 0 < rho < r0 the union of the   *)
(* components of Omega meeting Omega_rho has finitely many components and is *)
(* a compact set K together with finitely many disjoint strong 2eps-horns,   *)
(* each disjoint from Omega_rho with boundary in Omega_(rho/2C) (finiteness  *)
(* by volume counting).  Corrected: the last stage separates along neck      *)
(* spheres (apx_sphere_sep; MT Prop A.21 is built for that case).  Body:     *)
(* P2C_LEMMA_11_30_STATEMENT.                                                *)

let P2_LEMMA_11_30_STATEMENT = new_definition
 `P2_LEMMA_11_30_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps (hs:(A)rfs_history) r0 gl rho.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
         apx_sphere_sep (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
         rfs_pinched (rfs_view hs) /\
         (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                ==> p3_canon_at (rfs_view hs) C eps x t) /\
         rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
           (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
         &0 < rho /\ rho < r0
         ==> ?(J:num->bool) H K.
               FINITE J /\
               FINITE {U | U IN connected_components_of
                                (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
                           ~(U INTER p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs)
                                                  gl rho = {})} /\
               (!j. j IN J
                    ==> p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (&2 * eps)
                                (H j) /\
                        DISJOINT (p3_horn_set (H j))
                                 (p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl rho) /\
                        IMAGE (H j) (sphere(vec 0,&1)) SUBSET
                        p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl
                                     (rho / (&2 * C))) /\
               (!i j. i IN J /\ j IN J /\ ~(i = j)
                      ==> DISJOINT (p3_horn_set (H i)) (p3_horn_set (H j))) /\
               compact_in (hs_top hs (hs_count hs)) K /\
               UNIONS {U | U IN connected_components_of
                                (subtopology (hs_top hs (hs_count hs)) (p3_omega hs)) /\
                           ~(U INTER p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs)
                                                  gl rho = {})} =
               K UNION UNIONS {p3_horn_set (H j) | j IN J}`;;

(* MT Thm 11.31 (p. 287; used pp. 359, 361; Def 15.5): the surgery scale     *)
(* function hf (h(rho,delta) <= min(rho delta, rho / 2C), rho = delta r0):   *)
(* in a strong 2eps-horn of Omega with boundary in Omega_(rho/2C), points    *)
(* with R >= hf^-2 are centres of strong delta-necks in the maximal          *)
(* extension inside the horn, and some y with R(y) = hf^-2 has one whose     *)
(* central sphere cuts off an end of the horn disjoint from Omega_rho (the   *)
(* plus side, toward the end).  Corrected: the stages separate along neck    *)
(* spheres (apx_sphere_sep).  Body: P2C_THM_11_31_STATEMENT.  The neck at y  *)
(* is an evolving delta-neck of rescaled backward length 2                   *)
(* (rfs_evolving_neck with len = 2), rather than a strong one (len = 1):     *)
(* MT p. 406 (Lemma 17.7) needs strong necks centred at the points of the    *)
(* surgery neck, where R may be below R(y).  The proof of MT (p. 291) gives  *)
(* the round shrinking cylinder on (-infinity, 0] as the limit, so any fixed *)
(* backward length follows.  The component of Omega minus the central sphere *)
(* of the neck at y that contains e(2 basis 1) lies in the image under H of  *)
(* the points of norm > 1 (MT Lemma 15.11, step S3, needs it).               *)

let P2_THM_11_31_STATEMENT = new_definition
 `P2_THM_11_31_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps. &1 < C /\ &0 < eps /\ eps <= eps0
        ==> ?hf. p3_hfun C hf /\
              !(hs:(A)rfs_history) r0 gl dl H.
                 rfs_history_ok hs /\ &0 < r0 /\ rfs_pinched (rfs_view hs) /\
                 (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k)) /\
                 (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                        inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                        ==> p3_canon_at (rfs_view hs) C eps x t) /\
                 rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                   (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
                 &0 < dl /\ dl < &1 /\
                 p3_horn (p3_maxext hs (p3_omega hs) gl) (rfs_horizon hs) (&2 * eps) H /\
                 IMAGE H (sphere(vec 0,&1)) SUBSET
                 p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl
                              (dl * r0 / (&2 * C))
                 ==> (!x. x IN p3_horn_set H /\
                          inv(hf (dl * r0) dl pow 2) <=
                          mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                          ==> ?e. rfs_strong_neck (p3_maxext hs (p3_omega hs) gl) dl x
                                                  (rfs_horizon hs) e /\
                                  IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set H) /\
                     (?y e R1.
                        y IN p3_horn_set H /\
                        mfd_scalar (hs_atlas hs (hs_count hs)) gl y = inv(hf (dl * r0) dl pow 2) /\
                        rfs_evolving_neck (p3_maxext hs (p3_omega hs) gl) dl y (rfs_horizon hs) (&2) e /\
                        IMAGE e (rfs_neck_dom dl) SUBSET p3_horn_set H /\
                        (!z. R1 <= norm z
                             ==> H z IN p3_horn_end (subtopology (hs_top hs (hs_count hs))
                                                                 (p3_omega hs)) H e) /\
                        DISJOINT (p3_horn_end (subtopology (hs_top hs (hs_count hs))
                                                           (p3_omega hs)) H e)
                                 (p3_omega_rho (hs_atlas hs (hs_count hs)) (p3_omega hs) gl
                                               (dl * r0)) /\
                        connected_component_of
                          (subtopology (hs_top hs (hs_count hs))
                                       (p3_omega hs DIFF IMAGE e (sphere(vec 0,&1))))
                          (e(&2 % basis 1)) SUBSET IMAGE H {z | &1 < norm z})`;;

(* MT Lemma 12.3 (p. 295; used pp. 331, 354, 360, 398, 404, 410): a standard *)
(* initial metric exists (p3_std_initial: Def 12.1 structure), the closed    *)
(* surgery cap B(0, A0 + 4) has volume <= K, and D^-1 <= R <= D.             *)

let P2_LEMMA_12_3_STATEMENT = new_definition
 `P2_LEMMA_12_3_STATEMENT <=>
    ?g0 A0 K D.
       p3_std_initial g0 A0 /\ &0 < K /\ &1 <= D /\
       (?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0
              {x | p3_std_dist g0 x < A0 + &4} v /\ v <= K) /\
       (!x. inv D <= mfd_scalar (open_set_atlas (:real^3)) g0 x /\
            mfd_scalar (open_set_atlas (:real^3)) g0 x <= D)`;;

(* MT Thm 12.5 without uniqueness (p. 296; used pp. 399, 401, 404, 405):     *)
(* uniqueness (12.5(1), used only in Lemma 16.8) is avoided; standard flows  *)
(* exist; every partial standard flow extends to a standard flow             *)
(* (P2_STD_EXTEND); every standard flow lives on [0,1), has complete         *)
(* positively curved slices for t > 0, is SO(3)-invariant and asymptotic to  *)
(* the shrinking cylinder; the constants of Props 12.7, 12.31 and Thm 12.32  *)
(* are uniform over all standard flows (from the compactness of the space of *)
(* standard solutions, Kleiner-Lott).                                        *)

let P2_THM_12_5_STATEMENT = new_definition
 `P2_THM_12_5_STATEMENT <=>
    !g0 A0. p3_std_initial g0 A0
      ==> (?G. p3_std_flow g0 (&1) G) /\
          !te G. p3_std_flow g0 te G
                 ==> te = &1 /\
                     (!t. &0 < t /\ t < &1
                          ==> mfd_complete (euclidean,open_set_atlas (:real^3)) (G t) /\
                              !x u v. ~collinear {vec 0,u,v}
                                      ==> &0 < mfd_sectional (open_set_atlas (:real^3)) (G t)
                                                             x u v) /\
                     (!t Q x. &0 <= t /\ t < &1 /\ orthogonal_matrix Q /\ det Q = &1
                              ==> transp Q ** G t (Q ** x) ** Q = G t x) /\
                     (!t0 eps. &0 <= t0 /\ t0 < &1 /\ &0 < eps
                               ==> ?X. compact X /\
                                       !x. ~(x IN X)
                                           ==> ?e. mfd_param euclidean (open_set_atlas (:real^3))
                                                     (rfs_neck_dom eps) e /\
                                                   x IN IMAGE e (sphere(vec 0,&1)) /\
                                                   rfs_close_fam (rfs_kreg eps) eps
                                                     {s | &0 <= s /\ s <= t0} (rfs_neck_dom eps)
                                                     cylinder_flow
                                                     (\s y. rfs_pullback (open_set_atlas (:real^3))
                                                                         e (G s) y))`;;

let P2_STD_EXTEND_STATEMENT = new_definition
 `P2_STD_EXTEND_STATEMENT <=>
    !g0 A0 te G.
       p3_std_initial g0 A0 /\ p3_partial_std g0 te G
       ==> ?G'. p3_std_flow g0 (&1) G' /\
                !t x. &0 <= t /\ t < te ==> G' t x = G t x`;;

(* MT Prop 12.7 (p. 299; used p. 377 Claim 16.14): outside a large ball,    *)
(* uniform over all standard flows, the flow on [0,T'] (T' < 1) is           *)
(* eps-close, in the cylinder coordinates of the standard initial metric, to *)
(* the shrinking cylinder.                                                   *)

let P2_PROP_12_7_STATEMENT = new_definition
 `P2_PROP_12_7_STATEMENT <=>
    !g0 A0 Tp eps.
       p3_std_initial g0 A0 /\ &0 <= Tp /\ Tp < &1 /\ &0 < eps
       ==> ?A1. A0 <= A1 /\
                !G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t <= Tp /\ A1 < p3_std_dist g0 x
                      ==> lck_dist2 (rfs_kreg eps)
                            (mpullback (p3_std_nc g0 A0) (cylinder_flow t)) (G t) x
                          < eps pow 2`;;

(* MT Prop 12.31 (p. 325; used pp. 376, 399, 404): R >= c/(1-t) on every    *)
(* standard flow, c uniform.                                                 *)

let P2_PROP_12_31_STATEMENT = new_definition
 `P2_PROP_12_31_STATEMENT <=>
    !g0 A0.
       p3_std_initial g0 A0
       ==> ?c. &0 < c /\
               !G t x. p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1
                     ==> c / (&1 - t) <= mfd_scalar (open_set_atlas (:real^3)) (G t) x`;;

(* MT Thm 12.32 (p. 326; used pp. 401, 405, constant C' p. 354): every point *)
(* (x,t), 0 < t < 1, of every standard flow (C' uniform; the uses have t >   *)
(* 0; at t = 0 far points are only necks of length 0) is in the core of a    *)
(* (C'(eps),eps)-cap, or the centre of an evolving eps-neck from time 0      *)
(* whose initial slice is at distance >= 1 from the surgery cap (as given by *)
(* the proof, used p. 405), or the centre of an evolving eps-neck of         *)
(* normalized length 1 + eps.  Corrected: for 0 < eps <= eps0 only (the      *)
(* proof goes through Thm 12.28 and Cor 9.95).  Body:                        *)
(* P2C_THM_12_32_STATEMENT.                                                  *)

let P2_THM_12_32_STATEMENT = new_definition
 `P2_THM_12_32_STATEMENT <=>
    ?eps0. &0 < eps0 /\
     !g0 A0 eps.
       p3_std_initial g0 A0 /\ &0 < eps /\ eps <= eps0
       ==> ?C'. &1 < C' /\
                !G x t. p3_std_flow g0 (&1) G /\ &0 < t /\ t < &1
                      ==> (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t) C' eps U Y /\
                                 x IN Y) \/
                          (?e. rfs_evolving_neck
                                 (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                {s | &0 <= s /\ s < &1} G)
                                 eps x t (t * mfd_scalar (open_set_atlas (:real^3)) (G t) x) e /\
                               !z. z IN IMAGE e (rfs_neck_dom eps)
                                   ==> A0 + &5 <= p3_std_dist g0 z) \/
                          (?e. rfs_evolving_neck
                                 (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                {s | &0 <= s /\ s < &1} G)
                                 eps x t (&1 + eps) e)`;;

(* MT Lemma 12.37 (p. 328; used p. 332 Claim 13.1, Thm 13.2(3)): the radial *)
(* map from the cylinder (neck coordinates, metric cylinder_flow 0) to the  *)
(* standard initial metric does not increase lengths where s < A0 + 4.     *)

let P2_LEMMA_12_37_STATEMENT = new_definition
 `P2_LEMMA_12_37_STATEMENT <=>
    !g0 A0 y v.
       p3_std_initial g0 A0 /\ ~(y = vec 0) /\ sqrt(&2) * log(norm y) < A0 + &4
       ==> (jacobian (p3_std_radial g0 A0) (at y) ** v) dot
           (g0 (p3_std_radial g0 A0 y) ** (jacobian (p3_std_radial g0 A0) (at y) ** v)) <=
           v dot (cylinder_flow (&0) y ** v)`;;

