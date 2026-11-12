(* ========================================================================= *)
(* Unit pc_p2c_iface (Part 2C): the statement constants of Part 2C and the   *)
(* derivations between them.                                                 *)
(*                                                                           *)
(* The first part gives the forms of MT's statements that Part 2C proves (MT *)
(* Prop 5.14 / Thm 5.15, Lemma 11.2, Lemma 11.23, Thm 11.19, Thm 11.8, Lemma *)
(* 11.30, Thm 11.31, Thm 12.32), corrected where MT's text needs it.  The    *)
(* Part 2 statements of pc_p3_iface have the same texts, except              *)
(* P2_LEMMA_11_23_STATEMENT, which is false as written; the theorems named   *)
(* ..._WEAKER derive each P2C_ form from its P2_ form.  Part A states the    *)
(* results that Part 2C uses from other layers (the P2C_REQ_ statements),    *)
(* Part B the internal statements of the Part 2C units, and Part C derives   *)
(* the Part 2C theorems from them (P2C_FULL_CHAIN).                          *)
(*                                                                           *)
(* pc_cmp_defs is loaded for cmp_expmetric, pc_apx_ncreq for APX_A25_NC_ENDS *)
(* (Lemma 11.30) and pc_p2b_kreq for the Part 2B class vocabulary and the    *)
(* FIX forms of the kappa-solution statements.                               *)
(* ========================================================================= *)

needs "src/pc_p2c_views.ml";;
needs "src/pc_apx_defs.ml";;
needs "src/pc_geo_defs.ml";;
needs "src/pc_cmp_defs.ml";;
needs "src/pc_apx_ncreq.ml";;
needs "src/pc_p2b_kreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* MT Prop 5.14 / Thm 5.15.  Two changes to MT's statement: (i) if J has a   *)
(* least element a0 (forward limits, J = [0,theta) or J = {0}), the rescaled *)
(* derivative bounds abs(nabla^l Rm) <= C(A,l) at time a0 are assumed (MT's  *)
(* endpoint needs Thm 3.29; without them the time-a0 slices need not         *)
(* converge smoothly: metrics with bounded curvature and oscillating         *)
(* curvature, e.g. a C^2-bounded but C^3-unbounded perturbation of the round *)
(* S^3 as initial data); (ii) completeness is asserted at s = 0 always, and  *)
(* at the times of an interval [a,b] containing 0 when the curvature bound   *)
(* there is uniform in A (MT's proof uses a bound independent of A).  In     *)
(* addition the least element of J, if any, is 0, so (i) only applies with   *)
(* a0 = 0 (a deliberate restriction).  A least element a0 < 0 would need the *)
(* flow extended down to a0 by a Shi estimate from the bottom (a shift of    *)
(* the base time does not work: the CG limit at the shifted base can contain *)
(* regions that do not persist); a use with a closed bottom shrinks J to an  *)
(* interval without least element.  P2_THM_5_15_STATEMENT has the same text. *)
(* ------------------------------------------------------------------------- *)

let P2C_THM_5_15_STATEMENT = new_definition
 `P2C_THM_5_15_STATEMENT (u:A->bool) (w:B->bool) <=>
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

(* ------------------------------------------------------------------------- *)
(* MT Lemma 11.2.  The proof uses abs(dR/ds) <= C R^(3/2) along curves and   *)
(* abs(dR/dt) <= C R^2 along flow lines at points with strong canonical      *)
(* neighbourhoods.  Caps and C-components carry these bounds (rfs_cap,       *)
(* rfs_c_component; for C-components MT's definition does not, and here the  *)
(* bounds are part of it), but necks and eps-round components only through   *)
(* closeness: on an eps-neck abs(dR/dt) / R^2 is close to 1 (the shrinking   *)
(* cylinder), so the bounds need eps <= eps0 (and [1/eps] >= 4 for the       *)
(* Laplacian of R) and C >= 2.  MT's statement has neither (for eps          *)
(* large the neck alternative is a C^0 condition and gives no control of the *)
(* gradient: steep funnels are counterexamples).  Also MT's bound (11.1)     *)
(* needs R(z) >= 0 (a point near z with R(z) < 0 can have R in (r0^-2,       *)
(* (16/9) r0^-2]), so R(z) is replaced by max 0 R(z) in the time window and  *)
(* the conclusion (no change when R(z) >= 0).  P2_LEMMA_11_2_STATEMENT has   *)
(* the same text.                                                            *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_2_STATEMENT = new_definition
 `P2C_LEMMA_11_2_STATEMENT (u:A->bool) <=>
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

(* The core form for regular views, with the derivative bounds as explicit   *)
(* hypotheses (any C > 0; this is the comparison argument of MT pp.          *)
(* 268-269), and the bridge from canonical neighbourhoods to the bounds.     *)
(* Forward in time (t0 < t') the ball must be carried from the slice at t0   *)
(* by the identity (MT: the embedding of B(z,t0,r') x I is compatible with   *)
(* time); p2c_regular_view relates slices only after the initial time of a   *)
(* persistence interval (histories satisfy it since their slabs are          *)
(* [T_k,T_k+1), P2C_HISTORY_SLAB_RIGHT).                                     *)

let P2C_LEMMA_11_2_DB_STATEMENT = new_definition
 `P2C_LEMMA_11_2_DB_STATEMENT (u:A->bool) <=>
    !V C r0 z t0 t' r'.
       p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                           (real->A->real^3^3)) /\
       &0 < C /\ &0 < r0 /\
       (!x t. min t0 t' <= t /\ t <= max t0 t' /\ x IN topspace(rfs_vtop V t) /\
              inv(r0 pow 2) <= rfs_vscalar V t x
              ==> sqrt(rfs_scalar_grad2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                  C * rfs_vscalar V t x * sqrt(rfs_vscalar V t x) /\
                  abs(rfs_scalar_lap (rfs_vatlas V t) (rfs_vmetric V t) x +
                      &2 * rfs_ric_norm2 (rfs_vatlas V t) (rfs_vmetric V t) x) <=
                  C * rfs_vscalar V t x pow 2) /\
       z IN topspace(rfs_vtop V t0) /\ &0 < r' /\
       r' <= inv(&2 * C * sqrt(max (rfs_vscalar V t0 z) (inv(r0 pow 2)))) /\
       abs(t' - t0) <= inv(&16 * C * (max (&0) (rfs_vscalar V t0 z) + inv(r0 pow 2))) /\
       rfs_persists V (rfs_vball V t0 z r') (min t0 t') (max t0 t') /\
       (t0 < t'
        ==> mfd_diffeo (rfs_vtop V t0) (rfs_vatlas V t0) (rfs_vball V t0 z r')
                       (rfs_vtop V t') (rfs_vatlas V t') (rfs_vball V t0 z r')
                       (\y:A. y) (\y. y))
       ==> !s y. min t0 t' < s /\ s <= max t0 t' /\ y IN rfs_vball V t0 z r'
                 ==> rfs_vscalar V s y <= &2 * (max (&0) (rfs_vscalar V t0 z) + inv(r0 pow 2))`;;

let P2C_CANON_DERIV_STATEMENT = new_definition
 `P2C_CANON_DERIV_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !top atlas g C eps x U.
         smooth_manifold_atlas (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ &1 < C /\ &0 < eps /\ eps <= eps0 /\
         rfs_canonical_nbhd (top,atlas) g C eps x U
         ==> &0 < mfd_scalar atlas g x /\
             sqrt(rfs_scalar_grad2 atlas g x) <=
             max C (&2) * mfd_scalar atlas g x * sqrt(mfd_scalar atlas g x) /\
             abs(rfs_scalar_lap atlas g x + &2 * rfs_ric_norm2 atlas g x) <=
             max C (&2) * mfd_scalar atlas g x pow 2`;;

(* ------------------------------------------------------------------------- *)
(* MT Lemma 11.23 / Claim 17.6.  P2_LEMMA_11_23_STATEMENT is false at        *)
(* event times: a retained point x next to a new cap may have necks at       *)
(* earlier times that reach into the discarded region while at the event    *)
(* time no (2C,2eps)-neighbourhood exists (general cut-and-cap events allow *)
(* any cap metric, e.g. one with R < 0 next to the cut).  Correction: the    *)
(* earlier neighbourhoods lie in a compact K of the slice at t inside a set  *)
(* W persisting over (t - eta, t] (this also gives the smooth point and the  *)
(* flow line of P2_LEMMA_11_23_STATEMENT).  At non-event times K is the      *)
(* whole stage.                                                              *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_23_STATEMENT = new_definition
 `P2C_LEMMA_11_23_STATEMENT (u:A->bool) <=>
    ?Kc eps0. &1 <= Kc /\ &0 < eps0 /\
      !C eps (hs:(A)rfs_history) x t eta W K.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < eta /\
         x IN K /\ compact_in (rfs_top_at hs t) K /\ K SUBSET W /\
         rfs_persists (rfs_view hs) W (t - eta) t /\
         (!s. t - eta < s /\ s < t
              ==> ?U. rfs_strong_canonical (rfs_view hs) C eps x s U /\ U SUBSET K)
         ==> p3_canon_at (rfs_view hs) (&2 * C) (Kc * eps) x t`;;

(* MT Thm 11.19 (items (1) and (5)) with the cap factor Kc: the limits of    *)
(* caps are (2C, Kc eps)-caps (re-centring of the end necks), so the         *)
(* canonical neighbourhoods in the maximal extension are (2C, Kc eps) ones;  *)
(* uses take eps <= eps' / Kc.  The clause holds for EVERY limit metric gl   *)
(* and is typed (p3_canon_typed): 2 eps necks, Kc eps caps and round         *)
(* components, 2 <= Kc.  P2_THM_11_19_STATEMENT has the same text            *)
(* (P2C_THM_11_19_WEAKER).                                                   *)

let P2C_THM_11_19_STATEMENT = new_definition
 `P2C_THM_11_19_STATEMENT (u:A->bool) <=>
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

(* ------------------------------------------------------------------------- *)
(* MT Thm 11.8 with kappa-solutions in the sense of MT Def 9.2               *)
(* (p2c_kappa_sol: smooth up to time 0) with abs Rm bounded on every [a,0]   *)
(* (p2b_kappa_solution); P2_THM_11_8_STATEMENT has the same body             *)
(* (P2C_THM_11_8_WEAKER).  The limit is not asked to be a p3_kappa_solution, *)
(* i.e. a Ricci flow on (-inf,b) with b > 0: the limit flow exists only on   *)
(* (-inf,0] and continuing it needs short-time existence for complete        *)
(* noncompact data (not in the PDE layer).  The bound on [a,0] comes from    *)
(* the bound of each slice (Prop 2.19) and the derivative bound dR/dt <= C   *)
(* R^2 at canonical neighbourhoods by compactness of [a,0] (MT, Prop 11.10,  *)
(* uses Harnack there, which needs the bound itself).  The stages are        *)
(* assumed to separate along neck spheres (apx_sphere_sep), because MT's     *)
(* proof goes through Thm 10.2, which uses MT Prop A.21, and the Appendix    *)
(* layer treats the separating case only; on the route of Part 3 the stages  *)
(* have simply connected components (APX_SC_SPHERE_SEP_STATEMENT).  With MT  *)
(* Cor 11.16, |Rm| is bounded on B(x_inf,0,A) x (-T0,0] for every A (the T'  *)
(* < infinity step of Prop 17.1, p. 408).                                    *)
(* ------------------------------------------------------------------------- *)

let P2C_THM_11_8_STATEMENT = new_definition
 `P2C_THM_11_8_STATEMENT (u:A->bool) (w:B->bool) <=>
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

(* ------------------------------------------------------------------------- *)
(* MT Lemma 11.30 uses MT Prop A.21 (unions of necks and caps along X0 are   *)
(* tubes or capped tubes), which the Appendix layer provides only under      *)
(* apx_sphere_sep; MT Thm 11.31 uses Thm 10.2 (Claim 11.33) in the maximal   *)
(* extension.  The same hypothesis is added (it passes to Omega by           *)
(* APX_SEP_OPEN_STATEMENT).  P2_LEMMA_11_30_STATEMENT and                    *)
(* P2_THM_11_31_STATEMENT have the same texts.                               *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_30_STATEMENT = new_definition
 `P2C_LEMMA_11_30_STATEMENT (u:A->bool) <=>
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

(* In the second clause the neck at y is an evolving dl-neck of rescaled     *)
(* backward length 2 (len = 1 is a strong neck), as Part 3 needs at MT p.    *)
(* 406 (Lemma 17.7); the proof of MT (p. 291) gives the round shrinking      *)
(* cylinder on (-infinity, 0] as the limit, so any fixed backward length     *)
(* follows.  Also in the second clause, the component of Omega minus the     *)
(* central sphere of the neck at y that contains e(2 e_1) (the plus side)    *)
(* lies in the open horn H(norm z > 1), so the sphere does not bound a ball  *)
(* inside the horn (MT pp. 287, 292).                                        *)

let P2C_THM_11_31_STATEMENT = new_definition
 `P2C_THM_11_31_STATEMENT (u:A->bool) <=>
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

(* ------------------------------------------------------------------------- *)
(* MT Thm 12.32 holds for 0 < eps <= eps0: its proof goes through Thm        *)
(* 12.28 (eps < 1) and Cor 9.95 (eps <= eps'), and for large eps the neck of *)
(* case (3) must reach back 1 + eps normalized times, which smaller eps do   *)
(* not give.  The uses (MT pp. 401, 405) have eps = beta eps / 3, small.     *)
(* ------------------------------------------------------------------------- *)

let P2C_THM_12_32_STATEMENT = new_definition
 `P2C_THM_12_32_STATEMENT <=>
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

(* ------------------------------------------------------------------------- *)
(* The corrected forms are implied by the statements of pc_p3_iface (the     *)
(* theorems named ..._WEAKER); P2C_LEMMA_11_2_NONNEG is the corrected Lemma  *)
(* 11.2 when R(z) >= 0.                                                      *)
(* ------------------------------------------------------------------------- *)

let P2C_LEMMA_11_2_NONNEG = prove
 (`!u:A->bool.
     P2C_LEMMA_11_2_STATEMENT u
     ==> ?eps0. &0 < eps0 /\
           !(hs:(A)rfs_history) C eps r0 z t0 t' r'.
              rfs_history_ok hs /\ &2 <= C /\ &0 < eps /\ eps <= eps0 /\ &0 < r0 /\
              (!x t. min t0 t' <= t /\ t <= max t0 t' /\ x IN topspace(rfs_top_at hs t) /\
                     inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                     ==> p3_canon_at (rfs_view hs) C eps x t) /\
              z IN topspace(rfs_top_at hs t0) /\ &0 <= rfs_vscalar (rfs_view hs) t0 z /\
              &0 < r' /\
              r' <= inv(&2 * C * sqrt(max (rfs_vscalar (rfs_view hs) t0 z) (inv(r0 pow 2)))) /\
              abs(t' - t0) <= inv(&16 * C * (rfs_vscalar (rfs_view hs) t0 z + inv(r0 pow 2))) /\
              rfs_persists (rfs_view hs) (rfs_vball (rfs_view hs) t0 z r') (min t0 t') (max t0 t')
              ==> !s y. min t0 t' < s /\ s <= max t0 t' /\ y IN rfs_vball (rfs_view hs) t0 z r'
                        ==> rfs_vscalar (rfs_view hs) s y <=
                            &2 * (rfs_vscalar (rfs_view hs) t0 z + inv(r0 pow 2))`,
  GEN_TAC THEN REWRITE_TAC[P2C_LEMMA_11_2_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eps0:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `max (&0) (rfs_vscalar (rfs_view (hs:(A)rfs_history)) t0 (z:A)) =
                rfs_vscalar (rfs_view hs) t0 z` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[]);;

let P2C_THM_12_32_WEAKER = prove
 (`P2_THM_12_32_STATEMENT ==> P2C_THM_12_32_STATEMENT`,
  REWRITE_TAC[P2_THM_12_32_STATEMENT; P2C_THM_12_32_STATEMENT] THEN
  DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `eps:real`]) THEN
  ASM_REWRITE_TAC[]);;

let P2C_LEMMA_11_23_WEAKER = prove
 (`!u:A->bool. P2_LEMMA_11_23_STATEMENT u ==> P2C_LEMMA_11_23_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_11_23_STATEMENT; P2C_LEMMA_11_23_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`&2`; `eps0:real`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&1 <= &2`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `x:A`;
                                `t:real`; `eta / &2`]) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rfs_smooth_pt] THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `eta:real`] THEN ASM SET_TAC[];
    REWRITE_TAC[p3_flowline] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `s':real` THEN STRIP_TAC THEN
    UNDISCH_TAC `rfs_persists (rfs_view hs) (W:A->bool) (t - eta) t` THEN
    REWRITE_TAC[rfs_view; rfs_persists] THEN DISCH_THEN(MP_TAC o SPEC `s':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN ASM SET_TAC[];
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN REWRITE_TAC[p3_canon_at] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]]]);;

let P2C_THM_11_19_WEAKER = prove
 (`!u:A->bool. P2_THM_11_19_STATEMENT u ==> P2C_THM_11_19_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_THM_11_19_STATEMENT; P2C_THM_11_19_STATEMENT] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let P2C_THM_5_15_WEAKER = prove
 (`!(u:A->bool) (w:B->bool). P2_THM_5_15_STATEMENT u w ==> P2C_THM_5_15_STATEMENT u w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2_THM_5_15_STATEMENT; P2C_THM_5_15_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`;
                       `Q:num->real`; `J:real->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`;
                                `Q:num->real`; `J:real->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; IN_REAL_INTERVAL]);;



let P2C_THM_11_8_WEAKER = prove
 (`!(u:A->bool) (w:B->bool). P2_THM_11_8_STATEMENT u w ==> P2C_THM_11_8_STATEMENT u w`,
  REWRITE_TAC[P2_THM_11_8_STATEMENT; P2C_THM_11_8_STATEMENT]);;

let P2C_LEMMA_11_30_WEAKER = prove
 (`!u:A->bool. P2_LEMMA_11_30_STATEMENT u ==> P2C_LEMMA_11_30_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_LEMMA_11_30_STATEMENT; P2C_LEMMA_11_30_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let P2C_THM_11_31_WEAKER = prove
 (`!u:A->bool. P2_THM_11_31_STATEMENT u ==> P2C_THM_11_31_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2_THM_11_31_STATEMENT; P2C_THM_11_31_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* The results of the other layers that Part 2C uses, as exact statements:   *)
(* Part 2B, the appendix, the Ricci flow and PDE units, comparison geometry. *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part A. Statements used from other layers.                               *)
(* ========================================================================= *)

(* MT Thm 1.36 with Prop 1.35 and Bishop-Gromov Thm 1.34, local form: a      *)
(* curvature bound and a volume lower bound on a ball with compact closure   *)
(* give an injectivity radius lower bound at the centre                      *)
(* (Cheeger-Gromov-Taylor).  Used by Cor 5.10 (P2C_CG_COMPACT).              *)

let P2C_REQ_CGT_STATEMENT = new_definition
 `P2C_REQ_CGT_STATEMENT (u:A->bool) <=>
    !K r v0. &0 < K /\ &0 < r /\ &0 < v0
      ==> ?i0. &0 < i0 /\ i0 < r /\
            !top atlas g x.
               hausdorff_space (top:A topology) /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ x IN topspace top /\
               compact_in top (top closure_of mfd_ball (top,atlas) g x r) /\
               (!y. y IN mfd_ball (top,atlas) g x r ==> mfd_rm_norm atlas g y <= K) /\
               (?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r) v /\ v0 <= v)
               ==> mfd_inj_ball (top,atlas) g x i0`;;

(* MT Thm 10.2 for generalized flows, as MT states it: the view form of      *)
(* P2_THM_10_2_STATEMENT, for regular pinched views with time set in [0,inf) *)
(* (the standard solution and maximal extensions are not histories), with    *)
(* apx_sphere_sep on the slices (the Appendix layer treats the separating    *)
(* case only; on our route every slice separates).                           *)

let P2C_REQ_THM_10_2_VIEW_STATEMENT = new_definition
 `P2C_REQ_THM_10_2_VIEW_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps C A. &0 < eps /\ eps <= eps0 /\ &1 < C /\ &0 < A
        ==> ?D0 D. &0 < D0 /\ &0 < D /\
              !V x t.
                 p2c_regular_view (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) /\
                 rfs_pinched V /\ (!s. s < &0 ==> rfs_vtop V s = discrete_topology {}) /\
                 (!s. apx_sphere_sep (rfs_vtop V s) (rfs_vatlas V s)) /\
                 x IN topspace(rfs_vtop V t) /\
                 (!y s. s <= t /\ y IN topspace(rfs_vtop V s) /\
                        &4 * rfs_vscalar V t x <= rfs_vscalar V s y
                        ==> p3_canon_at V C eps y s) /\
                 D0 <= rfs_vscalar V t x
                 ==> !y. y IN rfs_vball V t x (A * inv(sqrt(rfs_vscalar V t x)))
                         ==> rfs_vscalar V t y <= D * rfs_vscalar V t x`;;

(* MT Cor 9.95 with Cor 9.94, view form, neck alternative of normalized      *)
(* length L: used by MT Thm 12.28 (canonical neighbourhoods of the standard  *)
(* solution with evolving necks for rescaled time 1 + eps).  For L = 1 and   *)
(* history views this is P2_COR_9_95_STATEMENT (with the MT Def 9.2 form of  *)
(* kappa-solutions).  Orientability is asked of non-empty slices only (empty *)
(* slices of flow views are not manifolds).                                  *)

let P2C_REQ_COR_9_95_VIEW_STATEMENT = new_definition
 `P2C_REQ_COR_9_95_VIEW_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?epsp. &0 < epsp /\
      !eps L. &0 < eps /\ eps <= epsp /\ &1 <= L
        ==> ?C95. &1 < C95 /\
              !C V x t Q top atlas g xl kappa.
                 C95 <= C /\
                 (!n. p2c_regular_view (V n:(real->A topology)#
                                            (real->((A->bool)#(A->real^3))->bool)#
                                            (real->A->real^3^3)) /\
                      x n IN topspace(rfs_vtop (V n) (t n)) /\
                      !s. ~(topspace(rfs_vtop (V n) s) = {})
                          ==> mfd_orientable (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
                 (!Tl. &0 < Tl ==> p3_flow_limit V x t Q (top:B topology,atlas) g xl Tl) /\
                 p2c_kappa_sol kappa (top,atlas) g
                 ==> ?N. !n. N <= n
                             ==> (?e. rfs_evolving_neck (V n) eps (x n) (t n) L e) \/
                                 (?U Y. rfs_cap (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                                                (rfs_vmetric (V n) (t n)) C eps U Y /\
                                        x n IN Y) \/
                                 (?U. x n IN U /\
                                      rfs_c_component (rfs_vtop (V n) (t n),
                                                       rfs_vatlas (V n) (t n))
                                                      (rfs_vmetric (V n) (t n)) C U) \/
                                 (?U. x n IN U /\
                                      rfs_round_component (rfs_vtop (V n) (t n),
                                                           rfs_vatlas (V n) (t n))
                                                          (rfs_vmetric (V n) (t n)) eps U)`;;

(* MT Prop 2.19 for nonnegative curvature (with the strong maximum           *)
(* principle): a complete nonnegatively curved time-0 slice of a flow on     *)
(* (a,0] whose points with R > 4 have (C,eps)-canonical neighbourhoods has   *)
(* bounded curvature (positively curved: no small necks; otherwise the       *)
(* universal cover splits).  Used by Claims 11.7, 11.17 and the end of the   *)
(* proof of Thm 11.8.                                                        *)

let P2C_REQ_NONNEG_BOUNDED_STATEMENT = new_definition
 `P2C_REQ_NONNEG_BOUNDED_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas a g.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         hausdorff_space (top:A topology) /\ a < &0 /\
         rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a (&0) g /\
         connected_space top /\ mfd_complete (top,atlas) (g (&0)) /\
         (!t x u v. a < t /\ t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g t) x u v) /\
         (!x. x IN topspace top /\ &4 < mfd_scalar atlas (g (&0)) x
              ==> ?U. rfs_canonical_nbhd (top,atlas) (g (&0)) C eps x U)
         ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g (&0)) x <= K`;;

(* MT Thm 9.93(6)-(7) with Cor 9.50: a kappa-solution all of whose points at *)
(* all times are centres of 2eps-necks is the shrinking round cylinder:      *)
(* every point is the centre of a strong delta-neck for every delta > 0.     *)
(* Used by Thm 11.31.                                                        *)

let P2C_REQ_KAPPA_NECKS_ROUND_STATEMENT = new_definition
 `P2C_REQ_KAPPA_NECKS_ROUND_STATEMENT (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !eps kappa top atlas g.
         &0 < eps /\ eps <= eps0 /\ p2c_kappa_sol kappa (top:B topology,atlas) g /\
         (!t x. t <= &0 /\ x IN topspace top ==> ?e. rfs_neck (top,atlas) (g t) eps x e)
         ==> !delta t x. &0 < delta /\ t <= &0 /\ x IN topspace top
                         ==> ?e. rfs_strong_neck (rfs_flow_view (top,atlas) {s | s <= &0} g)
                                                 delta x t e`;;

(* MT Thm 9.59: asymptotic volume ratio zero.  Used by MT Claim 12.30 and    *)
(* the proof of Prop 12.31.                                                  *)

let P2C_REQ_AVR_ZERO_STATEMENT = new_definition
 `P2C_REQ_AVR_ZERO_STATEMENT (w:B->bool) <=>
    !kappa top atlas g x eps.
       p2c_kappa_sol kappa (top:B topology,atlas) g /\ x IN topspace top /\ &0 < eps
       ==> ?A v. &0 < A /\
                 mfd_has_volume (top,atlas) (g (&0)) (mfd_ball (top,atlas) (g (&0)) x A) v /\
                 v < eps * A pow 3`;;

(* MT Lemma 11.13 (Toponogov).                                              *)

let P2C_REQ_LEMMA_11_13_STATEMENT = new_definition
 `P2C_REQ_LEMMA_11_13_STATEMENT (u:A->bool) <=>
    !top atlas g x0.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ connected_space top /\ ~compact_space top /\
       mfd_complete (top,atlas) g /\ x0 IN topspace top /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v)
       ==> ?D. &0 < D /\
               !y. y IN topspace top /\ D <= mfd_dist (top,atlas) g x0 y
                   ==> ?x. x IN topspace top /\
                           mfd_dist (top,atlas) g y x = mfd_dist (top,atlas) g x0 y /\
                           &3 / &2 * mfd_dist (top,atlas) g x0 y < mfd_dist (top,atlas) g x0 x`;;

(* MT Claims 11.34-11.35 (the splitting theorem 2.13 with Lemma A.2): a      *)
(* complete nonnegatively curved 3-manifold with two ends (a compact K whose *)
(* complement has two components with non-compact closures) contains no      *)
(* (C,eps)-cap for eps small.                                                *)

let P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT = new_definition
 `P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g.
         &0 < C /\ &0 < eps /\ eps <= eps0 /\ hausdorff_space (top:A topology) /\
         smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
         riemannian_metric atlas g /\ connected_space top /\ mfd_complete (top,atlas) g /\
         (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas g x u v) /\
         (?K U1 U2. compact_in top K /\
                    U1 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                    U2 IN connected_components_of (subtopology top (topspace top DIFF K)) /\
                    ~(U1 = U2) /\ ~compact_in top (top closure_of U1) /\
                    ~compact_in top (top closure_of U2))
         ==> !U Y. ~rfs_cap (top,atlas) g C eps U Y`;;

(* MT Prop 9.79 part (1), cap case, type preserving: a (C,eps)-cap U with x  *)
(* in its core, carried by a diffeomorphism psi whose pullback metric is     *)
(* delta-close on U at the scale R(x), contains a (C',eps')-cap whose core   *)
(* contains psi x.  Used with P2C_REQ_TWO_ENDS_NO_CAP in Claim 11.35: caps   *)
(* of the approximants phi_n(K) x {t} are carried to the complete limit      *)
(* slice (which has two ends), with (C,eps) -> (2C,2eps), and excluded there *)
(* (MT runs the argument in the approximants).                               *)

let P2C_REQ_PROP_9_79_CAP_STATEMENT = new_definition
 `P2C_REQ_PROP_9_79_CAP_STATEMENT (u:A->bool) (w:B->bool) <=>
    !C eps C' eps'. &1 < C /\ C < C' /\ &0 < eps /\ eps < eps' /\ eps' < &1 / &4
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U Y psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\
               rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U' Y'. U' SUBSET IMAGE psi U /\
                           rfs_cap (top',atlas') g' C' eps' U' Y' /\ psi x IN Y'`;;

(* MT Thm 4.37, Hamilton's trace Harnack inequality, ancient or from time a: *)
(* dR/dt >= -R/(t - a) for complete flows with nonnegative bounded           *)
(* curvature.  Used by Claim 11.12, Prop 11.10, Thm 11.8.                    *)

let P2C_REQ_HARNACK_STATEMENT = new_definition
 `P2C_REQ_HARNACK_STATEMENT (u:A->bool) <=>
    !top atlas a b g K x t D.
       hausdorff_space (top:A topology) /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       (!s. a < s /\ s < b ==> mfd_complete (top,atlas) (g s)) /\
       (!s y u v. a < s /\ s < b /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas (g s) y u v) /\
       (!s y. a < s /\ s < b /\ y IN topspace top ==> mfd_rm_norm atlas (g s) y <= K) /\
       a < t /\ t < b /\ x IN topspace top /\
       ((\s. mfd_scalar atlas (g s) x) has_real_derivative D) (atreal t)
       ==> --(mfd_scalar atlas (g t) x / (t - a)) <= D`;;

(* MT Cor 3.26, Hamilton's distance distortion, in integrated form with a    *)
(* time-dependent bound Ric <= 2 k(t) g, n = 3.  Used by Claim 11.12.        *)

let P2C_REQ_DIST_DISTORTION_STATEMENT = new_definition
 `P2C_REQ_DIST_DISTORTION_STATEMENT (u:A->bool) <=>
    !top atlas a b g k t1 t2 x y.
       hausdorff_space (top:A topology) /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       (!s. a < s /\ s < b ==> mfd_complete (top,atlas) (g s)) /\
       a < t1 /\ t1 <= t2 /\ t2 < b /\ x IN topspace top /\ y IN topspace top /\
       k real_continuous_on real_interval[t1,t2] /\
       (!s. t1 <= s /\ s <= t2 ==> &0 < k s) /\
       (!s z v. t1 <= s /\ s <= t2 /\ z IN topspace top
                ==> mfd_ricci atlas (g s) z v v <= &2 * k s * (v dot (g s z ** v)))
       ==> mfd_dist (top,atlas) (g t1) x y <=
           mfd_dist (top,atlas) (g t2) x y +
           real_integral (real_interval[t1,t2]) (\s. &8 * sqrt(&2 * k s / &3))`;;

(* MT Prop 4.1: on a closed manifold min R is non-decreasing.  Used by Cor   *)
(* 11.16 (compact limits).                                                   *)

let P2C_REQ_SCALAR_MIN_STATEMENT = new_definition
 `P2C_REQ_SCALAR_MIN_STATEMENT (u:A->bool) <=>
    !top atlas a b g t1 t2 x.
       hausdorff_space (top:A topology) /\ compact_space top /\
       ricci_flow_on (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       a < t1 /\ t1 <= t2 /\ t2 < b /\ x IN topspace top
       ==> ?y. y IN topspace top /\ mfd_scalar atlas (g t1) y <= mfd_scalar atlas (g t2) x`;;

(* MT Cor 4.20 as a local strong maximum principle for the curvature         *)
(* operator: nonnegative sectional curvature that is positive at one point   *)
(* at the initial time is positive everywhere at later times on a connected  *)
(* manifold (no compactness).  Used by MT Lemma 12.6 / Thm 12.5(3).          *)

let P2C_REQ_SMP_POS_STATEMENT = new_definition
 `P2C_REQ_SMP_POS_STATEMENT (u:A->bool) <=>
    !top atlas a b g x0.
       hausdorff_space (top:A topology) /\ connected_space top /\
       ricci_flow_from (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       (!t x u v. a <= t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas (g t) x u v) /\
       x0 IN topspace top /\
       (!u v. ~collinear {vec 0,u,v} ==> &0 < mfd_sectional atlas (g a) x0 u v)
       ==> !t x u v. a < t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                     ==> &0 < mfd_sectional atlas (g t) x u v`;;

(* MT Cor 4.14 (Hamilton): on closed 3-manifolds nonnegative sectional       *)
(* curvature is preserved.  Used for the compact approximations of the       *)
(* standard solution (Sec 12.3 and the restarts).                            *)

let P2C_REQ_SEC_PRESERVED_STATEMENT = new_definition
 `P2C_REQ_SEC_PRESERVED_STATEMENT (u:A->bool) <=>
    !top atlas a b g.
       hausdorff_space (top:A topology) /\ compact_space top /\
       ricci_flow_from (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas (g a) x u v)
       ==> !t x u v. a <= t /\ t < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                     ==> &0 <= mfd_sectional atlas (g t) x u v`;;

(* Uniqueness for complete flows with bounded curvature, extending the       *)
(* compact energy uniqueness of pc_rf_unique (Kotschwar's weighted energy,   *)
(* the method of FrenzyMath M35): two complete Ricci flows of bounded        *)
(* curvature on compact time intervals with the same initial metric of       *)
(* bounded geometry agree, given a proper exhaustion function with bounded   *)
(* gradient and Laplacian whose sublevel sets have volume at most C exp(C    *)
(* s).  Without the volume bound the weighted-energy method fails (H^3 with  *)
(* phi = log(1 + r^2) / 2 meets the other hypotheses, volume growth like     *)
(* exp(2 e^s)); the result itself is Chen-Zhu.  This is the uniqueness used  *)
(* by route (U) for the standard solution.                                   *)

let P2C_REQ_UNIQ_COMPLETE_STATEMENT = new_definition
 `P2C_REQ_UNIQ_COMPLETE_STATEMENT (u:A->bool) <=>
    !top atlas a b g g' phi C.
       hausdorff_space (top:A topology) /\
       ricci_flow_from (top,atlas:((A->bool)#(A->real^3))->bool) a b g /\
       ricci_flow_from (top,atlas) a b g' /\
       (!x. x IN topspace top ==> g' a x = g a x) /\
       (!t. a <= t /\ t < b ==> mfd_complete (top,atlas) (g t) /\
                                mfd_complete (top,atlas) (g' t)) /\
       (!b1. b1 < b
             ==> ?K. !t x. a <= t /\ t <= b1 /\ x IN topspace top
                           ==> mfd_rm_norm atlas (g t) x <= K /\
                               mfd_rm_norm atlas (g' t) x <= K) /\
       (!l. ?Cl. !x. x IN topspace top
                     ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas x) (g a))
                                         (SND(chart_at atlas x) x) <= Cl) /\
       mfd_smooth atlas (lift o phi) /\
       (!c. compact_in top {x | x IN topspace top /\ phi x <= c}) /\
       (!x. x IN topspace top
            ==> p2c_fgrad2 atlas (g a) phi x <= C /\ abs(p2c_flap atlas (g a) phi x) <= C) /\
       (!s v. mfd_has_volume (top,atlas) (g a) {x | x IN topspace top /\ phi x <= s} v
              ==> v <= C * exp(C * s))
       ==> !t x. a <= t /\ t < b /\ x IN topspace top ==> g' t x = g t x`;;

(* MT Thm 1.34, Bishop-Gromov, the nonnegatively curved case: Vol B(x,r) /   *)
(* r^3 is non-increasing.  Used by MT Claim 12.30 and Prop 12.31 (small      *)
(* rescaled volumes give small volumes of fixed balls).                      *)

let P2C_REQ_BISHOP_GROMOV_STATEMENT = new_definition
 `P2C_REQ_BISHOP_GROMOV_STATEMENT (u:A->bool) <=>
    !top atlas g x r1 r2 v1 v2.
       hausdorff_space (top:A topology) /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g y u v) /\
       x IN topspace top /\ &0 < r1 /\ r1 <= r2 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r1) v1 /\
       mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x r2) v2
       ==> v2 / r2 pow 3 <= v1 / r1 pow 3`;;

(* ------------------------------------------------------------------------- *)
(* The corrected Part 2B forms P2C_REQ_SLICE_FIX, P2C_REQ_NECK_FIX,          *)
(* P2C_REQ_CAP_FIX, P2C_REQ_NONNEG_BOUNDED_FIX and P2C_REQ_SLICE_LOCAL (the  *)
(* texts of the Part 2B units under Part 2C names).  The routes of Part 2C   *)
(* use them in place of P2_PROP_9_79_SLICE / NECK and P2C_REQ_PROP_9_79_CAP, *)
(* which are false as written, and of P2C_REQ_NONNEG_BOUNDED, which needs    *)
(* separation; those statements stay defined but no route uses them.         *)
(* P2C_REQ_SLICE_LOCAL is for an incomplete target (the slice Omega of a     *)
(* maximal extension, MT Thm 11.19): P2C_REQ_SLICE_FIX with completeness of  *)
(* the target replaced by compactness of the closure of the image            *)
(* (meaningful with the guard in clause (7) of rfs_cap, pc_rfs_geom).  The   *)
(* corrected forms of P2C_REQ_COR_9_95_VIEW, P2C_REQ_KAPPA_NECKS_ROUND and   *)
(* P2C_REQ_AVR_ZERO are the FIX forms of pc_p2b_kreq.  P2C_REQ_NECK_FIX asks *)
(* for a regular source view and riemannian metrics on the target slices;    *)
(* P2C_REQ_SLICE_FIX and P2C_REQ_CAP_FIX take a bound Kr on the squared      *)
(* norms of Rm, nabla Rm and nabla^2 Rm of the normalized metric R(x) g on U *)
(* (delta depends on Kr), and so does P2C_REQ_SLICE_LOCAL; the routes that   *)
(* feed history slices into them supply this bound.                          *)
(* ------------------------------------------------------------------------- *)

let P2C_REQ_SLICE_FIX_STATEMENT = new_definition
 `P2C_REQ_SLICE_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
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

let P2C_REQ_NECK_FIX_STATEMENT = new_definition
 `P2C_REQ_NECK_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
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

let P2C_REQ_CAP_FIX_STATEMENT = new_definition
 `P2C_REQ_CAP_FIX_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U Y psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\ mfd_complete (top',atlas') g' /\
               rfs_cap (top,atlas) g C eps U Y /\ x IN Y /\
               (!y l. y IN U /\ l <= 2
                      ==> lrm_deriv_norm2 l
                            (metric_local atlas (chart_at atlas y)
                               (\z. mfd_scalar atlas g x %% g z))
                            (SND(chart_at atlas y) y) <= Kr) /\
               mfd_diffeo top atlas U top' atlas' (IMAGE psi U) psi psi' /\
               rfs_mclose (rfs_kreg delta) delta atlas U
                 (\y. mfd_scalar atlas g x %% g y)
                 (\y. mfd_scalar atlas g x %% mfd_pullback_metric atlas atlas' psi g' y)
               ==> ?U' Y'. U' SUBSET IMAGE psi U /\
                           rfs_cap (top',atlas') g' C' eps' U' Y' /\ psi x IN Y'`;;

let P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT = new_definition
 `P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas a g.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         hausdorff_space (top:A topology) /\ a < &0 /\
         rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a (&0) g /\
         connected_space top /\ mfd_complete (top,atlas) (g (&0)) /\
         apx_sphere_sep top atlas /\
         (!t x u v. a < t /\ t <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g t) x u v) /\
         (!x. x IN topspace top /\ &4 < mfd_scalar atlas (g (&0)) x
              ==> ?U. rfs_canonical_nbhd (top,atlas) (g (&0)) C eps x U)
         ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g (&0)) x <= K`;;

let P2C_REQ_SLICE_LOCAL_STATEMENT = new_definition
 `P2C_REQ_SLICE_LOCAL_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?K eps0. &1 <= K /\ &0 < eps0 /\
      !C eps C' eps' Kr. &1 < C /\ &2 * C <= C' /\ &0 < eps /\ K * eps <= eps' /\
                         eps' <= eps0
      ==> ?delta. &0 < delta /\
            !top atlas g top' atlas' g' x U psi psi'.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               riemannian_metric atlas g /\ hausdorff_space top' /\
               smooth_manifold_atlas top' (atlas':((B->bool)#(B->real^3))->bool) /\
               riemannian_metric atlas' g' /\
               compact_in top' (top' closure_of IMAGE psi U) /\
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

(* ========================================================================= *)
(* Part B: internal statements of the Part 2C units (compactness, blow-up    *)
(* limits, the singular time, the standard solution); the regularity         *)
(* statements of views are in pc_p2c_views.                                  *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Cheeger-Gromov compactness (unit pc_p2c_cg; MT Thm 5.6, Lemma 5.7, Thm    *)
(* 5.9, Cor 5.10) for the time slices of views, rescaled by Q n: balls of    *)
(* every radius with compact closure, all derivatives of Rm bounded on them, *)
(* a volume lower bound at the base point: a subsequence converges to a      *)
(* complete limit on the carrier B (the uses take B = real^3).               *)

let P2C_CG_COMPACT_STATEMENT = new_definition
 `P2C_CG_COMPACT_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q.
       (!n. hausdorff_space (rfs_vtop (V n) (t n)) /\
            smooth_manifold_atlas (rfs_vtop (V n) (t n)) (rfs_vatlas (V n) (t n)) /\
            riemannian_metric (rfs_vatlas (V n) (t n)) (rfs_vmetric (V n) (t n)) /\
            (x n:A) IN topspace(rfs_vtop (V n) (t n)) /\ &0 < Q n) /\
       (!A. &0 < A
            ==> ?N. !n. N <= n
                        ==> compact_in (rfs_vtop (V n) (t n))
                              (rfs_vtop (V n) (t n) closure_of
                               rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n))))) /\
       (!A l. &0 < A
              ==> ?CAl N. !n y. N <= n /\
                                y IN rfs_vball (V n) (t n) (x n) (A * inv(sqrt(Q n)))
                                ==> p3_vderiv2 (V n) l (t n) y <= CAl * Q n pow (l + 2)) /\
       (?r0 kappa N. &0 < r0 /\ &0 < kappa /\
          !n. N <= n
              ==> ?v. mfd_has_volume (rfs_vtop (V n) (t n),rfs_vatlas (V n) (t n))
                        (rfs_vmetric (V n) (t n))
                        (rfs_vball (V n) (t n) (x n) (r0 * inv(sqrt(Q n)))) v /\
                      kappa * (r0 * inv(sqrt(Q n))) pow 3 <= v)
       ==> ?sub (top:B topology) atlas g xl.
              p3_subseq sub /\
              p3_slice_limit (\n. V (sub n)) (x o sub) (t o sub) (Q o sub) (top,atlas) g xl`;;

(* MT Lemma 5.7 (proved as P2C_GAUGE in the unit pc_p2c_gauge): the gauge of *)
(* Cheeger-Gromov compactness.  In normal coordinates w |-> exp_x(E w) (E    *)
(* an orthonormal frame at x), on a tangent ball of radius rho inside the    *)
(* domain of exp_x, with C 0 rho^2 <= 1 and |nabla^l Rm|^2 <= C l^2          *)
(* (l <= k) on the metric ball B(x,rho), the pulled-back metric is a         *)
(* metric field on ball(0,rho) and its squared C^k distance from the         *)
(* Euclidean metric is bounded on ball(0,rho'), rho' < rho, by a constant    *)
(* depending only on k, C, rho, rho'.                                        *)

let P2C_GAUGE_STATEMENT = new_definition
 `P2C_GAUGE_STATEMENT (u:A->bool) <=>
    !k (C:num->real) rho rho'.
       (!l. &0 <= C l) /\ &0 < rho' /\ rho' < rho /\ C 0 * rho pow 2 <= &1
       ==> ?B. !top atlas (g:A->real^3^3) x E.
             hausdorff_space top /\ smooth_manifold_atlas top atlas /\
             riemannian_metric atlas g /\ x IN topspace top /\
             mfd_orthonormal_frame g x E /\
             mfd_tball g x rho SUBSET mfd_exp_dom (top,atlas) g x /\
             (!y l. y IN mfd_ball (top,atlas) g x rho /\ l <= k
                    ==> lrm_deriv_norm2 l (metric_local atlas (chart_at atlas y) g)
                                          (SND(chart_at atlas y) y) <= C l pow 2)
             ==> metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) g x E) /\
                 !w. norm w < rho'
                     ==> lck_dist2 k (\z:real^3. mat 1) (cmp_expmetric (top,atlas) g x E) w
                         <= B`;;

(* Hamilton compactness over a given time-0 limit (the flowlim route,        *)
(* pc_p2c_fl514; MT Prop 5.14 with the endpoint correction): if J has a      *)
(* least element it is 0 (forward limits use the C^infinity convergence at   *)
(* time 0 and Shi with initial bounds, P2_THM_3_29).  The limit keeps the    *)
(* exhaustion W, the maps phi (along the subsequence) and the initial slice  *)
(* g0, so for the standard solution and the caps the limit lives on          *)
(* (euclidean, open_set_atlas (:real^3)) with initial metric g0.             *)

(* P2C_PROP_5_14_STATEMENT is defined in pc_p3_iface. *)

(* Blow-up limits of pinched views have nonnegative curvature (unit          *)
(* pc_p2c_t533; MT Thm 5.33, Hamilton-Ivey through rfs_pinched_at).  The     *)
(* limit metrics are Riemannian (the convergence lck_dist2 is measured with  *)
(* the limit metric itself, so a degenerate limit would make it and          *)
(* mfd_sectional meaningless).                                               *)

let P2C_THM_5_33_STATEMENT = new_definition
 `P2C_THM_5_33_STATEMENT (u:A->bool) (w:B->bool) <=>
    !V x t Q J top atlas g xl.
       (!n. p2c_regular_view (V n:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) /\
            rfs_pinched (V n) /\ (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {})) /\
       (!B. ?N. !n. N <= n ==> B < Q n) /\
       p3_flow_limit_on V x t Q J (top:B topology,atlas) g xl /\
       (!s. s IN J ==> riemannian_metric atlas (g s))
       ==> !s y u v. s IN J /\ y IN topspace top /\ ~collinear {vec 0,u,v}
                     ==> &0 <= mfd_sectional atlas (g s) y u v`;;

(* Blow-up limits for short times (unit pc_p2c_blowup; MT Thm 11.1 with Cors *)
(* 11.3-11.4, Claims 11.5-11.7), view form.  MT hypothesis (4) of Thms 11.1  *)
(* and 11.8 (p. 267) has compact closures of the balls B(x n,t n,A Q         *)
(* n^-1/2), which Cor 5.10 and Shi need; it is a hypothesis here and in      *)
(* P2C_THM_11_8_VIEW_STATEMENT, separate from p2c_vblowup_seq.  Without it   *)
(* the statement is false: the round shrinking S^3 minus a point.            *)

let P2C_THM_11_1_VIEW_STATEMENT = new_definition
 `P2C_THM_11_1_VIEW_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps kappa r0 mu V x t.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         p2c_vblowup_seq (C,eps,kappa,r0,mu)
           (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) x t /\
         (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
         (!A. ?N. !n. N <= n
                      ==> compact_in (rfs_vtop (V n) (t n))
                            (rfs_vtop (V n) (t n) closure_of
                             rfs_vball (V n) (t n) (x n)
                               (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))))
         ==> ?sub (top:B topology) atlas g xl T1 K.
                &0 < T1 /\ p3_subseq sub /\
                p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                  (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n))) (top,atlas) g xl T1 /\
                (!s. --T1 < s /\ s <= &0
                     ==> mfd_complete (top,atlas) (g s) /\
                         (!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                                  ==> &0 <= mfd_sectional atlas (g s) y u v) /\
                         (!y. y IN topspace top ==> mfd_rm_norm atlas (g s) y <= K))`;;

(* Long-time blow-up limits (unit pc_p2c_blowup; MT Thm 11.8 with Prop       *)
(* 11.10, Lemmas 11.11-11.13, Cor 11.16, Claim 11.17), view form.  With      *)
(* views of histories this gives P2C_THM_11_8_STATEMENT; with the flow view  *)
(* of a standard solution it is MT's use in Thms 12.28-12.29, Prop 12.31.    *)
(* With MT Cor 11.16, |Rm| is bounded on B(x_inf,0,A) x (-T0,0] for every A  *)
(* (the T' < infinity step of Prop 17.1, p. 408).                            *)

let P2C_THM_11_8_VIEW_STATEMENT = new_definition
 `P2C_THM_11_8_VIEW_STATEMENT (u:A->bool) (w:B->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps kappa r0 mu V x t.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\
         p2c_vblowup_seq (C,eps,kappa,r0,mu)
           (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) x t /\
         (!n s. apx_sphere_sep (rfs_vtop (V n) s) (rfs_vatlas (V n) s)) /\
         (!A. ?N. !n. N <= n
                      ==> compact_in (rfs_vtop (V n) (t n))
                            (rfs_vtop (V n) (t n) closure_of
                             rfs_vball (V n) (t n) (x n)
                               (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))))
         ==> (!T0. &0 < T0 /\ (!Tb. &0 < Tb /\ Tb < T0 ==> p2c_vblowup_back (kappa,r0) V x t Tb)
                   ==> ?sub (top:B topology) atlas g xl.
                          p3_subseq sub /\
                          p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                            (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
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
             ((!Tb. &0 < Tb ==> p2c_vblowup_back (kappa,r0) V x t Tb)
              ==> ?sub (top:B topology) atlas g xl.
                     p3_subseq sub /\
                     (!Tl. &0 < Tl
                           ==> p3_flow_limit (\n. V (sub n)) (x o sub) (t o sub)
                                 (\n. rfs_vscalar (V (sub n)) (t (sub n)) (x (sub n)))
                                 (top,atlas) g xl Tl) /\
                     p2b_kappa_solution kappa (top,atlas) g)`;;

(* The singular time (unit pc_p2c_sing; MT Lemma 11.21 = Thm 11.19 (1),     *)
(* (2), and MT's Lemma 11.23 with Claim 11.24 in the maximal extension =     *)
(* Thm 11.19 (5)).                                                            *)

let P2C_LEMMA_11_21_STATEMENT = new_definition
 `P2C_LEMMA_11_21_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps (hs:(A)rfs_history) r0.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
         rfs_pinched (rfs_view hs) /\
         (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                ==> p3_canon_at (rfs_view hs) C eps x t)
         ==> open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
             ?gl. rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                    (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl /\
                  (!c. compact_in (hs_top hs (hs_count hs))
                         {x | x IN p3_omega hs /\
                              mfd_scalar (hs_atlas hs (hs_count hs)) gl x <= c}) /\
                  (!x. x IN p3_omega hs
                       ==> --(&6) / (&4 * rfs_horizon hs + &1) <=
                           mfd_scalar (hs_atlas hs (hs_count hs)) gl x)`;;

(* Typed: 2 eps necks and Kc eps caps, 2 <= Kc.                             *)

let P2C_LEMMA_11_23_MAXEXT_STATEMENT = new_definition
 `P2C_LEMMA_11_23_MAXEXT_STATEMENT (u:A->bool) <=>
    ?Kc eps0. &2 <= Kc /\ &0 < eps0 /\
      !C eps (hs:(A)rfs_history) r0 gl.
         &1 < C /\ &0 < eps /\ eps <= eps0 /\ rfs_history_ok hs /\ &0 < r0 /\
         rfs_pinched (rfs_view hs) /\
         (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                inv(r0 pow 2) <= rfs_vscalar (rfs_view hs) t x
                ==> p3_canon_at (rfs_view hs) C eps x t) /\
         open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
         rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
           (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
         ==> !x. x IN p3_omega hs /\
                 inv(r0 pow 2) < mfd_scalar (hs_atlas hs (hs_count hs)) gl x
                 ==> p3_canon_typed (p3_maxext hs (p3_omega hs) gl) (&2 * C) (&2 * eps)
                                    (Kc * eps) x (rfs_horizon hs)`;;

(* The standard solution (units pc_p2c_stdinit, pc_p2c_stdflow), route (U):  *)
(* one standard flow Gs, constructed from compact doubles                    *)
(* (PDE_CURVATURE_TIME, Prop 5.14) and continued by restarts and gluing      *)
(* (PDE_GLUE), is unique among partial standard flows                        *)
(* (P2C_REQ_UNIQ_COMPLETE); all properties are proved for Gs and hold for    *)
(* every flow agreeing with Gs on [0,1).  P2C_STD_ASSEMBLY (below) derives   *)
(* P2_THM_12_5, P2_STD_EXTEND, P2_PROP_12_7, P2_PROP_12_31 and P2C_THM_12_32 *)
(* from P2C_STD_UNIQUE and P2C_STD_PROPS.                                    *)

(* phi also has sublevel sets of volume at most C exp(C s), the matching     *)
(* hypothesis of P2C_REQ_UNIQ_COMPLETE.                                      *)

let P2C_STD_BOUNDED_GEOM_STATEMENT = new_definition
 `P2C_STD_BOUNDED_GEOM_STATEMENT <=>
    !g0 A0.
       p3_std_initial g0 A0
       ==> (!l. ?Cl. !x. lrm_deriv_norm2 l (metric_local (open_set_atlas (:real^3))
                                              (chart_at (open_set_atlas (:real^3)) x) g0)
                                           (SND(chart_at (open_set_atlas (:real^3)) x) x)
                         <= Cl) /\
           ?phi C. mfd_smooth (open_set_atlas (:real^3)) (lift o phi) /\
                   (!c. compact {x:real^3 | phi x <= c}) /\
                   (!x. p2c_fgrad2 (open_set_atlas (:real^3)) g0 phi x <= C /\
                        abs(p2c_flap (open_set_atlas (:real^3)) g0 phi x) <= C) /\
                   (!s v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) g0
                                         {x:real^3 | phi x <= s} v
                          ==> v <= C * exp(C * s))`;;

let P2C_STD_PARTIAL_EXISTS_STATEMENT = new_definition
 `P2C_STD_PARTIAL_EXISTS_STATEMENT <=>
    !g0 A0. p3_std_initial g0 A0 ==> ?te G. &0 < te /\ p3_partial_std g0 te G`;;

let P2C_STD_UNIQUE_STATEMENT = new_definition
 `P2C_STD_UNIQUE_STATEMENT <=>
    !g0 A0 te te' G G'.
       p3_std_initial g0 A0 /\ p3_partial_std g0 te G /\ p3_partial_std g0 te' G'
       ==> !t x. &0 <= t /\ t < te /\ t < te' ==> G' t x = G t x`;;

let P2C_STD_PROPS_STATEMENT = new_definition
 `P2C_STD_PROPS_STATEMENT <=>
    ?eps0. &0 < eps0 /\
     !g0 A0.
       p3_std_initial g0 A0
       ==> ?Gs. p3_std_flow g0 (&1) Gs /\
                (!G. (!t x. &0 <= t /\ t < &1 ==> G t x = Gs t x)
                     ==> (!t. &0 < t /\ t < &1
                              ==> mfd_complete (euclidean,open_set_atlas (:real^3)) (G t) /\
                                  !x u v. ~collinear {vec 0,u,v}
                                          ==> &0 < mfd_sectional (open_set_atlas (:real^3))
                                                                 (G t) x u v) /\
                         (!t Q x. &0 <= t /\ t < &1 /\ orthogonal_matrix Q /\ det Q = &1
                                  ==> transp Q ** G t (Q ** x) ** Q = G t x) /\
                         (!t0 eps. &0 <= t0 /\ t0 < &1 /\ &0 < eps
                                   ==> ?X. compact X /\
                                           !x. ~(x IN X)
                                               ==> ?e. mfd_param euclidean
                                                         (open_set_atlas (:real^3))
                                                         (rfs_neck_dom eps) e /\
                                                       x IN IMAGE e (sphere(vec 0,&1)) /\
                                                       rfs_close_fam (rfs_kreg eps) eps
                                                         {s | &0 <= s /\ s <= t0}
                                                         (rfs_neck_dom eps) cylinder_flow
                                                         (\s y. rfs_pullback
                                                                  (open_set_atlas (:real^3))
                                                                  e (G s) y))) /\
                (!Tp eps. &0 <= Tp /\ Tp < &1 /\ &0 < eps
                          ==> ?A1. A0 <= A1 /\
                                   !G t x. (!t x. &0 <= t /\ t < &1 ==> G t x = Gs t x) /\
                                           &0 <= t /\ t <= Tp /\ A1 < p3_std_dist g0 x
                                           ==> lck_dist2 (rfs_kreg eps)
                                                 (mpullback (p3_std_nc g0 A0) (cylinder_flow t))
                                                 (G t) x < eps pow 2) /\
                (?c. &0 < c /\
                     !G t x. (!t x. &0 <= t /\ t < &1 ==> G t x = Gs t x) /\
                             &0 <= t /\ t < &1
                             ==> c / (&1 - t) <= mfd_scalar (open_set_atlas (:real^3)) (G t) x) /\
                (!eps. &0 < eps /\ eps <= eps0
                       ==> ?C'. &1 < C' /\
                                !G x t. (!t x. &0 <= t /\ t < &1 ==> G t x = Gs t x) /\
                                        &0 < t /\ t < &1
                                ==> (?U Y. rfs_cap (euclidean,open_set_atlas (:real^3)) (G t)
                                                   C' eps U Y /\ x IN Y) \/
                                    (?e. rfs_evolving_neck
                                           (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                          {s | &0 <= s /\ s < &1} G)
                                           eps x t
                                           (t * mfd_scalar (open_set_atlas (:real^3)) (G t) x) e /\
                                         !z. z IN IMAGE e (rfs_neck_dom eps)
                                             ==> A0 + &5 <= p3_std_dist g0 z) \/
                                    (?e. rfs_evolving_neck
                                           (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                                          {s | &0 <= s /\ s < &1} G)
                                           eps x t (&1 + eps) e))`;;

(* Flow views on (a,b] are regular: the companion of P2C_FLOW_VIEW_REGULAR   *)
(* (pc_p2c_views, views on [a,b)) for the limit flows of p3_flow_limit and   *)
(* kappa-solutions, which are rfs_flow_upto on (a,0]; used where such a      *)
(* limit is the source view of P2C_REQ_NECK_FIX.                             *)

let P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT = new_definition
 `P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT (u:A->bool) <=>
    !top atlas a b g.
       hausdorff_space (top:A topology) /\
       rfs_flow_upto (top,atlas:((A->bool)#(A->real^3))->bool) a b g
       ==> p2c_regular_view (rfs_flow_view (top,atlas) {s | a < s /\ s <= b} g)`;;

(* ========================================================================= *)
(* Part C: the standard-solution assembly (route U), Thm 11.19 from its      *)
(* halves, Lemma 11.2 and Thm 11.8 for histories from their core and view    *)
(* forms, the route statements and P2C_FULL_CHAIN.                           *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The standard solution.                                                   *)
(* ------------------------------------------------------------------------- *)

let P2C_STD_FLOW_AGREES = prove
 (`P2C_STD_UNIQUE_STATEMENT
   ==> !g0 A0 te (G:real->real^3->real^3^3) Gs.
          p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) Gs /\ p3_std_flow g0 te G
          ==> te = &1 /\ !t x. &0 <= t /\ t < &1 ==> G t x = Gs t x`,
  REWRITE_TAC[P2C_STD_UNIQUE_STATEMENT; p3_std_flow] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `te:real`;
                       `G:real->real^3->real^3^3`; `Gs:real->real^3->real^3^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t < te /\ t < &1
                      ==> (G:real->real^3->real^3^3) t x = Gs t x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `&1`; `te:real`;
                                  `Gs:real->real^3->real^3^3`;
                                  `G:real->real^3->real^3^3`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `te = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(te < &1) /\ ~(&1 < te) ==> te = &1`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(?te' G'. te < te' /\ p3_partial_std g0 te' G' /\
                             (!t. &0 <= t /\ t < te
                                  ==> G' t = (G:real->real^3->real^3^3) t))` THEN
      REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`&1`; `Gs:real->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `x:real^3` THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(?te' G'. &1 < te' /\ p3_partial_std g0 te' G' /\
                             (!t. &0 <= t /\ t < &1
                                  ==> G' t = (Gs:real->real^3->real^3^3) t))` THEN
      REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`te:real`; `G:real->real^3->real^3^3`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `x:real^3` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* Every partial standard flow lives at most up to time 1 and is extended by *)
(* the standard flow (uniqueness and maximality of Gs).                      *)

let P2C_STD_PARTIAL_AGREES = prove
 (`P2C_STD_UNIQUE_STATEMENT
   ==> !g0 A0 te (G:real->real^3->real^3^3) Gs.
          p3_std_initial g0 A0 /\ p3_std_flow g0 (&1) Gs /\ p3_partial_std g0 te G
          ==> te <= &1 /\ !t x. &0 <= t /\ t < te ==> Gs t x = G t x`,
  REWRITE_TAC[P2C_STD_UNIQUE_STATEMENT; p3_std_flow] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `te:real`;
                       `G:real->real^3->real^3^3`; `Gs:real->real^3->real^3^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!t x. &0 <= t /\ t < &1 /\ t < te
                      ==> (Gs:real->real^3->real^3^3) t x = G t x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`; `te:real`; `&1`;
                                  `G:real->real^3->real^3^3`;
                                  `Gs:real->real^3->real^3^3`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `te <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(?te' G'. &1 < te' /\ p3_partial_std g0 te' G' /\
                           (!t. &0 <= t /\ t < &1
                                ==> G' t = (Gs:real->real^3->real^3^3) t))` THEN
    REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`te:real`; `G:real->real^3->real^3^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real^3` THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;
let P2C_STD_ASSEMBLY = prove
 (`P2C_STD_UNIQUE_STATEMENT /\ P2C_STD_PROPS_STATEMENT
   ==> P2_THM_12_5_STATEMENT /\ P2_STD_EXTEND_STATEMENT /\ P2_PROP_12_7_STATEMENT /\
       P2_PROP_12_31_STATEMENT /\ P2C_THM_12_32_STATEMENT`,
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2C_STD_FLOW_AGREES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2C_STD_PARTIAL_AGREES) THEN
  UNDISCH_TAC `P2C_STD_PROPS_STATEMENT` THEN REWRITE_TAC[P2C_STD_PROPS_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[P2_THM_12_5_STATEMENT] THEN
    MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Gs:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [EXISTS_TAC `Gs:real->real^3->real^3^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`te:real`; `G:real->real^3->real^3^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `te = &1 /\ !t x. &0 <= t /\ t < &1 ==> (G:real->real^3->real^3^3) t x = Gs t x`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl) o SPEC `G:real->real^3->real^3^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    REWRITE_TAC[P2_STD_EXTEND_STATEMENT] THEN
    MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `te:real`;
                         `G:real->real^3->real^3^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Gs:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Gs:real->real^3->real^3^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[P2_PROP_12_7_STATEMENT] THEN
    MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `Tp:real`; `eps:real`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Gs:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`Tp:real`; `eps:real`]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A1:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[P2_PROP_12_31_STATEMENT] THEN
    MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Gs:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `t:real`; `x:real^3`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[P2C_THM_12_32_STATEMENT] THEN EXISTS_TAC `eps0:real` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`g0:real^3->real^3^3`; `A0:real`; `eps:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g0:real^3->real^3^3`; `A0:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Gs:real->real^3->real^3^3` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C':real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`G:real->real^3->real^3^3`; `x:real^3`; `t:real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;
(* ------------------------------------------------------------------------- *)
(* MT Thm 11.19 from its two halves: Lemma 11.21 (Omega open, the limit      *)
(* metric) and Lemma 11.23 in the maximal extension.                         *)
(* ------------------------------------------------------------------------- *)

let P2C_THM_11_19_FROM_PARTS = prove
 (`!u:A->bool. P2C_LEMMA_11_21_STATEMENT u /\ P2C_LEMMA_11_23_MAXEXT_STATEMENT u
               ==> P2C_THM_11_19_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_LEMMA_11_21_STATEMENT; P2C_LEMMA_11_23_MAXEXT_STATEMENT;
              P2C_THM_11_19_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `Kc:real` (X_CHOOSE_THEN `e2:real`
                                                       STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`Kc:real`; `min e1 e2:real`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`] o
                check (fun th -> length(fst(strip_forall(concl th))) = 4)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `gl:A->real^3^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `gl':A->real^3^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`C:real`; `eps:real`; `hs:(A)rfs_history`; `r0:real`;
                                `gl':A->real^3^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;

(* Lemma 11.2 for histories from its core form: strong canonical             *)
(* neighbourhoods give the derivative bounds with max C 2 = C, histories are *)
(* regular views.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Slabs are [T_k,T_k+1): a live slice is followed by slices of the same     *)
(* stage.                                                                    *)

let P2C_HISTORY_SLAB_RIGHT = prove
 (`!(hs:(A)rfs_history) t0 t'.
     rfs_history_ok hs /\ ~(topspace(rfs_top_at hs t0) = {}) /\ t0 < t'
     ==> ?s1. t0 < s1 /\ s1 <= t' /\
              rfs_top_at hs s1 = rfs_top_at hs t0 /\ rfs_atlas_at hs s1 = rfs_atlas_at hs t0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) t0` ASSUME_TAC THENL
   [UNDISCH_TAC `~(topspace(rfs_top_at (hs:(A)rfs_history) t0) = {})` THEN
    REWRITE_TAC[rfs_top_at] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`] RFS_SLAB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t0` THEN
    REWRITE_TAC[rfs_live; rfs_horizon] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) t0` THEN STRIP_TAC THEN
  EXISTS_TAC `min t' ((t0 + hs_time (hs:(A)rfs_history) (k + 1)) / &2)` THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) (k + 1) <= hs_time hs (hs_count hs + 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_live (hs:(A)rfs_history) (min t' ((t0 + hs_time hs (k + 1)) / &2)) /\
                rfs_slab hs (min t' ((t0 + hs_time hs (k + 1)) / &2)) = k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t0` THEN REWRITE_TAC[rfs_live] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[rfs_top_at; rfs_atlas_at] THEN ASM_REAL_ARITH_TAC);;

let P2C_LEMMA_11_2_FROM_DB = prove
 (`!u:A->bool. P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
               P2C_HISTORY_REGULAR_STATEMENT u
               ==> P2C_LEMMA_11_2_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P2C_LEMMA_11_2_DB_STATEMENT; P2C_CANON_DERIV_STATEMENT;
              P2C_HISTORY_REGULAR_STATEMENT; P2C_LEMMA_11_2_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`hs:(A)rfs_history`; `C:real`; `eps:real`; `r0:real`; `z:A`;
                       `t0:real`; `t':real`; `r':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `hs:(A)rfs_history`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `t0 < t'
    ==> mfd_diffeo (rfs_vtop (rfs_view (hs:(A)rfs_history)) t0) (rfs_vatlas (rfs_view hs) t0)
                   (rfs_vball (rfs_view hs) t0 z r')
                   (rfs_vtop (rfs_view hs) t') (rfs_vatlas (rfs_view hs) t')
                   (rfs_vball (rfs_view hs) t0 z r') (\y:A. y) (\y. y)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `t0:real`; `t':real`] P2C_HISTORY_SLAB_RIGHT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[p2c_regular_view] THEN
    DISCH_THEN(MP_TAC o SPECL [`rfs_vball (rfs_view (hs:(A)rfs_history)) t0 z r'`;
                               `t0:real`; `t':real`; `s1:real`] o el 3 o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `rfs_persists (rfs_view (hs:(A)rfs_history))
                       (rfs_vball (rfs_view hs) t0 z r') (min t0 t') (max t0 t')`) THEN
      SUBGOAL_THEN `min t0 t' = t0 /\ max t0 t' = t'` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rfs_view (hs:(A)rfs_history)`; `C:real`; `r0:real`; `z:A`;
                                `t0:real`; `t':real`; `r':real`] o
                check (fun th -> length(fst(strip_forall(concl th))) = 7)) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `z IN topspace(rfs_top_at (hs:(A)rfs_history) t0)` THEN
                  REWRITE_TAC[rfs_view; rfs_vtop]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `t:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN topspace(rfs_top_at (hs:(A)rfs_history) t)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN topspace (rfs_vtop (rfs_view (hs:(A)rfs_history)) t)` THEN
    REWRITE_TAC[rfs_view; rfs_vtop]; ALL_TAC] THEN
  SUBGOAL_THEN `p3_canon_at (rfs_view hs) C eps (x:A) t` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p3_canon_at] THEN DISCH_THEN(X_CHOOSE_TAC `U:A->bool`) THEN
  SUBGOAL_THEN `?U'. rfs_canonical_nbhd (rfs_top_at hs t,rfs_atlas_at hs t)
                       (rfs_metric_at (hs:(A)rfs_history) t) C eps (x:A) U'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_strong_canonical (rfs_view hs) C eps (x:A) t U` THEN
    REWRITE_TAC[rfs_view; rfs_strong_canonical; rfs_canonical_nbhd; rfs_strong_neck;
                rfs_evolving_neck] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < C` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (rfs_top_at (hs:(A)rfs_history) t) (rfs_atlas_at hs t) /\
                riemannian_metric (rfs_atlas_at hs t) (rfs_metric_at hs t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2c_regular_view (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[p2c_regular_view; rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT1) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`rfs_top_at (hs:(A)rfs_history) t`;
                                `rfs_atlas_at (hs:(A)rfs_history) t`;
                                `rfs_metric_at (hs:(A)rfs_history) t`; `C:real`; `eps:real`;
                                `x:A`; `U':A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `max C (&2) = C` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_view; rfs_vatlas; rfs_vmetric; rfs_vscalar] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Thm 11.8 for histories from its view form: history views are regular,     *)
(* empty before time 0, separate along neck spheres when the stages do, and  *)
(* backward flow lines give local persistence.                               *)
(* ------------------------------------------------------------------------- *)













(* Slices of histories are compact (for the compact-closure hypothesis of    *)
(* P2C_THM_11_8_VIEW_STATEMENT).                                             *)

let P2C_HIST_SLICE_COMPACT = prove
 (`!(hs:(A)rfs_history) t. rfs_history_ok hs ==> compact_space (rfs_top_at hs t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_top_at] THEN COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t` THEN
      REWRITE_TAC[rfs_live; rfs_horizon] THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN REWRITE_TAC[rfs_history_ok] THEN
    DISCH_THEN(MP_TAC o SPEC `rfs_slab (hs:(A)rfs_history) t` o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_EMPTY]]);;

let P2C_THM_11_8_FROM_VIEW = prove
 (`!(u:A->bool) (w:B->bool).
        P2C_THM_11_8_VIEW_STATEMENT u w /\ P2C_HISTORY_REGULAR_STATEMENT u /\
        P2C_HIST_FLOWLINE_PERSIST_STATEMENT u
        ==> P2C_THM_11_8_STATEMENT u w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P2C_THM_11_8_VIEW_STATEMENT; P2C_THM_11_8_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `eps0:real` STRIP_ASSUME_TAC)
                             STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eps0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
                       `hs:num->(A)rfs_history`; `x:num->A`; `t:num->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`C:real`; `eps:real`; `kappa:real`; `r0:real`; `mu:real`;
                                `\n. rfs_view ((hs:num->(A)rfs_history) n)`;
                                `x:num->A`; `t:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC P2C_BLOWUP_SEQ_HIST THEN EXISTS_TAC `u:A->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC P2C_HIST_SEP_SLICES THEN
      UNDISCH_TAC `p3_blowup_seq (C,eps,kappa,r0,mu) (hs:num->(A)rfs_history) x t` THEN
      REWRITE_TAC[p3_blowup_seq] THEN ASM_MESON_TAC[];
      X_GEN_TAC `A:real` THEN EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
      REWRITE_TAC[P2C_RFS_VIEW_PARTS] THEN MATCH_MP_TAC P2C_HIST_SLICE_COMPACT THEN
      UNDISCH_TAC `p3_blowup_seq (C,eps,kappa,r0,mu) (hs:num->(A)rfs_history) x t` THEN
      REWRITE_TAC[p3_blowup_seq] THEN MESON_TAC[]];
    REWRITE_TAC[GSYM P2C_BLOWUP_BACK_HIST]]);;

(* ------------------------------------------------------------------------- *)
(* Route statements: for each statement, the inputs of the MT proof as used  *)
(* (statement constants, proved in the Part 2C units and the other layers).  *)
(* u: carrier of histories; the limits live on real^3; d: carrier of the     *)
(* compact doubles approximating the standard initial metric.                *)
(* ------------------------------------------------------------------------- *)

let P2C_CG_COMPACT_ROUTE_STATEMENT = new_definition
 `P2C_CG_COMPACT_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2C_REQ_CGT_STATEMENT u /\ CMP_RELVOL_STATEMENT u (:3)
    ==> P2C_CG_COMPACT_STATEMENT u w`;;

let P2C_PROP_5_14_ROUTE_STATEMENT = new_definition
 `P2C_PROP_5_14_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2_THM_3_28_STATEMENT u /\ P2_THM_3_29_STATEMENT u ==> P2C_PROP_5_14_STATEMENT u w`;;

let P2C_THM_5_11_ROUTE_STATEMENT = new_definition
 `P2C_THM_5_11_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_CG_COMPACT_STATEMENT u (:real^3) /\ P2_THM_3_28_STATEMENT u /\
    P2C_HISTORY_REGULAR_STATEMENT u
    ==> P2_THM_5_11_STATEMENT u (:real^3)`;;

let P2C_THM_5_15_ROUTE_STATEMENT = new_definition
 `P2C_THM_5_15_ROUTE_STATEMENT (u:A->bool) <=>
    P2_THM_5_11_STATEMENT u (:real^3) /\ P2C_PROP_5_14_STATEMENT u (:real^3) /\
    P2_THM_3_28_STATEMENT u /\ P2_THM_3_29_STATEMENT u /\
    P2C_HISTORY_REGULAR_STATEMENT u
    ==> P2C_THM_5_15_STATEMENT u (:real^3)`;;

let P2C_HISTORY_REGULAR_ROUTE_STATEMENT = new_definition
 `P2C_HISTORY_REGULAR_ROUTE_STATEMENT (u:A->bool) <=>
    P3_LEMMA_14_11_STATEMENT u ==> P2C_HISTORY_REGULAR_STATEMENT u`;;

let P2C_LEMMA_11_2_ROUTE_STATEMENT = new_definition
 `P2C_LEMMA_11_2_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
    P2C_HISTORY_REGULAR_STATEMENT u
    ==> P2C_LEMMA_11_2_STATEMENT u`;;

(* The slice form of P2C_REQ_NONNEG_BOUNDED (Claim 11.7 and the -T slice of  *)
(* Prop 11.10 have no global flow; MT uses Prop 2.19 there) for both routes, *)
(* and P2B_REQ_FLAT_FORWARD (a flat slice stays flat) for the non-flat       *)
(* slices of the kappa-solution of Thm 11.8; both texts are in pc_p2b_kreq.  *)

let P2C_THM_11_1_VIEW_ROUTE_STATEMENT = new_definition
 `P2C_THM_11_1_VIEW_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT u /\
    P2C_CANON_DERIV_STATEMENT u /\ P2_THM_3_28_STATEMENT u /\
    P2C_CG_COMPACT_STATEMENT u w /\ P2C_PROP_5_14_STATEMENT u w /\
    P2C_THM_5_33_STATEMENT u w /\ P2C_REQ_SLICE_FIX_STATEMENT u w /\
    P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w
    ==> P2C_THM_11_1_VIEW_STATEMENT u w`;;

let P2C_THM_11_8_VIEW_ROUTE_STATEMENT = new_definition
 `P2C_THM_11_8_VIEW_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P2C_THM_11_1_VIEW_STATEMENT u w /\ P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
    P2C_REQ_HARNACK_STATEMENT w /\ P2C_REQ_DIST_DISTORTION_STATEMENT w /\
    P2C_REQ_LEMMA_11_13_STATEMENT w /\ P2C_REQ_SCALAR_MIN_STATEMENT w /\
    P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT w /\ P2C_PROP_5_14_STATEMENT u w /\
    P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
    P2_THM_3_28_STATEMENT u /\
    P2C_REQ_SLICE_FIX_STATEMENT u w /\ P2C_THM_5_33_STATEMENT u w /\
    APX_NO_CAP_IN_NECK_STATEMENT w /\ P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT w /\
    P2B_REQ_FLAT_FORWARD_STATEMENT w
    ==> P2C_THM_11_8_VIEW_STATEMENT u w`;;

let P2C_THM_11_8_ROUTE_STATEMENT = new_definition
 `P2C_THM_11_8_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_THM_11_8_VIEW_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
    P2C_HIST_FLOWLINE_PERSIST_STATEMENT u
    ==> P2C_THM_11_8_STATEMENT u (:real^3)`;;

let P2C_LEMMA_11_21_ROUTE_STATEMENT = new_definition
 `P2C_LEMMA_11_21_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
    P2_THM_3_28_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
    ==> P2C_LEMMA_11_21_STATEMENT u`;;

let P2C_LEMMA_11_23_ROUTE_STATEMENT = new_definition
 `P2C_LEMMA_11_23_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
    P2_THM_3_28_STATEMENT u /\
    P2C_REQ_SLICE_FIX_STATEMENT u u /\ P2C_REQ_NECK_FIX_STATEMENT u u /\
    P2C_HISTORY_REGULAR_STATEMENT u
    ==> P2C_LEMMA_11_23_STATEMENT u`;;

let P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT = new_definition
 `P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
    P2_THM_3_28_STATEMENT u /\
    P2C_REQ_SLICE_FIX_STATEMENT u u /\ P2C_REQ_NECK_FIX_STATEMENT u u /\
    P2C_REQ_SLICE_LOCAL_STATEMENT u u /\
    P2C_MAXEXT_REGULAR_STATEMENT u /\ P2C_HISTORY_REGULAR_STATEMENT u
    ==> P2C_LEMMA_11_23_MAXEXT_STATEMENT u`;;

(* Lemma 11.30 uses the relative end structure APX_A25_NC_ENDS               *)
(* (pc_apx_ncreq) for APX_A25_NC.                                            *)

let P2C_LEMMA_11_30_ROUTE_STATEMENT = new_definition
 `P2C_LEMMA_11_30_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_THM_11_19_STATEMENT u /\ P2C_LEMMA_11_21_STATEMENT u /\
    APX_A21_STATEMENT u /\ APX_A25_NC_ENDS_STATEMENT u /\ APX_NO_CAP_IN_NECK_STATEMENT u /\
    APX_SEP_OPEN_STATEMENT u
    ==> P2C_LEMMA_11_30_STATEMENT u`;;

(* The kappa-solution inputs are the Part 2B FIX forms (pc_p2b_kreq:         *)
(* p2b_kappa_solution and the class p2b_ksep): P2B_KAPPA_NECKS_ROUND_L_FIX   *)
(* (necks of every normalized length L) for 11.31, P2B_COR_9_95_VIEW_FIX and *)
(* P2B_AVR_ZERO_FIX for the standard solution; the forms of Part A are used  *)
(* by the Part 2B bridges.  The uses supply p2b_ksep (no orientability is    *)
(* asked of Thm 11.8).                                                       *)
(*                                                                           *)
(* Thm 11.8 in view form is an input; its first part (a limit on (-T0,0]     *)
(* under p2c_vblowup_back below T0) is the quantitative step of the backward *)
(* iteration of MT p. 291.                                                   *)

let P2C_THM_11_31_ROUTE_STATEMENT = new_definition
 `P2C_THM_11_31_ROUTE_STATEMENT (u:A->bool) <=>
    P2C_THM_11_1_VIEW_STATEMENT u (:real^3) /\ P2C_THM_11_8_VIEW_STATEMENT u (:real^3) /\
    P2C_REQ_THM_10_2_VIEW_STATEMENT u /\
    P2C_MAXEXT_REGULAR_STATEMENT u /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT (:real^3) /\
    P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\ APX_NECK_CURV_STATEMENT u /\
    P2C_REQ_NECK_FIX_STATEMENT (:real^3) u /\ P2C_REQ_SLICE_FIX_STATEMENT u (:real^3) /\
    P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT u /\
    P2C_THM_11_19_STATEMENT u /\ P2C_LEMMA_11_30_STATEMENT u /\ APX_SEP_OPEN_STATEMENT u /\
    P2C_REQ_CAP_FIX_STATEMENT u (:real^3) /\ P2_THM_3_28_STATEMENT u /\
    P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT (:real^3)
    ==> P2C_THM_11_31_STATEMENT u`;;

let P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT = new_definition
 `P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT (d:D->bool) <=>
    PDE_CURVATURE_TIME_STATEMENT d (:3) /\ P2C_PROP_5_14_STATEMENT d (:real^3) /\
    P2C_FLOW_VIEW_REGULAR_STATEMENT d /\ P2C_STD_BOUNDED_GEOM_STATEMENT
    ==> P2C_STD_PARTIAL_EXISTS_STATEMENT`;;

let P2C_STD_UNIQUE_ROUTE_STATEMENT = new_definition
 `P2C_STD_UNIQUE_ROUTE_STATEMENT <=>
    P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\ P2C_STD_BOUNDED_GEOM_STATEMENT
    ==> P2C_STD_UNIQUE_STATEMENT`;;

let P2C_STD_PROPS_ROUTE_STATEMENT = new_definition
 `P2C_STD_PROPS_ROUTE_STATEMENT (d:D->bool) <=>
    P2C_STD_PARTIAL_EXISTS_STATEMENT /\ P2C_STD_UNIQUE_STATEMENT /\
    P2C_STD_BOUNDED_GEOM_STATEMENT /\ P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
    PDE_CURVATURE_TIME_STATEMENT d (:3) /\ PDE_GLUE_STATEMENT (:real^3) (:3) /\
    P2C_REQ_SEC_PRESERVED_STATEMENT d /\ P2C_REQ_SMP_POS_STATEMENT (:real^3) /\
    P2C_PROP_5_14_STATEMENT d (:real^3) /\ P2C_PROP_5_14_STATEMENT (:real^3) (:real^3) /\
    P2_THM_3_28_STATEMENT (:real^3) /\ P2_THM_3_29_STATEMENT (:real^3) /\
    P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
    P2C_THM_11_8_VIEW_STATEMENT (:real^3) (:real^3) /\
    P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
    P2B_AVR_ZERO_FIX_STATEMENT (:real^3) /\ P2C_REQ_BISHOP_GROMOV_STATEMENT (:real^3) /\
    P2_LEMMA_3_14_STATEMENT (:real^3) /\ P2C_LEMMA_11_2_DB_STATEMENT (:real^3) /\
    P2C_CANON_DERIV_STATEMENT (:real^3) /\
    P2C_REQ_SLICE_FIX_STATEMENT (:real^3) (:real^3) /\
    P2C_REQ_NECK_FIX_STATEMENT (:real^3) (:real^3) /\
    APX_SC_SPHERE_SEP_STATEMENT (:real^3) /\
    P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT (:real^3)
    ==> P2C_STD_PROPS_STATEMENT`;;
(* Two of the route statements follow from the adapters above.              *)

let P2C_LEMMA_11_2_ROUTE = prove
 (`!u:A->bool. P2C_LEMMA_11_2_ROUTE_STATEMENT u`,
  REWRITE_TAC[P2C_LEMMA_11_2_ROUTE_STATEMENT; P2C_LEMMA_11_2_FROM_DB]);;

let P2C_THM_11_8_ROUTE = prove
 (`!u:A->bool. P2C_THM_11_8_ROUTE_STATEMENT u`,
  REWRITE_TAC[P2C_THM_11_8_ROUTE_STATEMENT; P2C_THM_11_8_FROM_VIEW]);;

(* ------------------------------------------------------------------------- *)
(* The full chain: the route statements, the internal statements (proved     *)
(* directly by the Part 2C units) and the external statements (Part A and    *)
(* the existing interfaces) imply the fifteen Part 2C theorems, in the       *)
(* corrected forms above where MT's statement needed a correction.           *)
(* ------------------------------------------------------------------------- *)

let P2C_STEP_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let P2C_FULL_CHAIN = prove
 (`!(u:A->bool) (d:D->bool).
     P2C_CG_COMPACT_ROUTE_STATEMENT u (:real^3) /\
     P2C_CG_COMPACT_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_PROP_5_14_ROUTE_STATEMENT u (:real^3) /\
     P2C_PROP_5_14_ROUTE_STATEMENT d (:real^3) /\
     P2C_PROP_5_14_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_THM_5_11_ROUTE_STATEMENT u /\ P2C_THM_5_15_ROUTE_STATEMENT u /\
     P2C_HISTORY_REGULAR_ROUTE_STATEMENT u /\
     P2C_THM_11_1_VIEW_ROUTE_STATEMENT u (:real^3) /\
     P2C_THM_11_1_VIEW_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT u (:real^3) /\
     P2C_THM_11_8_VIEW_ROUTE_STATEMENT (:real^3) (:real^3) /\
     P2C_LEMMA_11_21_ROUTE_STATEMENT u /\
     P2C_LEMMA_11_23_ROUTE_STATEMENT u /\ P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT u /\
     P2C_LEMMA_11_30_ROUTE_STATEMENT u /\ P2C_THM_11_31_ROUTE_STATEMENT u /\
     P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT d /\ P2C_STD_UNIQUE_ROUTE_STATEMENT /\
     P2C_STD_PROPS_ROUTE_STATEMENT d /\
     P2C_THM_5_33_STATEMENT u (:real^3) /\ P2C_THM_5_33_STATEMENT (:real^3) (:real^3) /\
     P2C_FLOW_VIEW_REGULAR_STATEMENT d /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P2C_FLOW_VIEW_REGULAR_UPTO_STATEMENT (:real^3) /\
     P2C_HIST_FLOWLINE_PERSIST_STATEMENT u /\ P2C_MAXEXT_REGULAR_STATEMENT u /\
     P2C_LEMMA_11_2_DB_STATEMENT u /\ P2C_LEMMA_11_2_DB_STATEMENT (:real^3) /\
     P2C_CANON_DERIV_STATEMENT u /\ P2C_CANON_DERIV_STATEMENT (:real^3) /\
     P2_LEMMA_12_3_STATEMENT /\ P2_LEMMA_12_37_STATEMENT /\ P2C_STD_BOUNDED_GEOM_STATEMENT /\
     P3_LEMMA_14_11_STATEMENT u /\
     P2_THM_3_28_STATEMENT u /\ P2_THM_3_29_STATEMENT u /\
     P2_THM_3_28_STATEMENT d /\ P2_THM_3_29_STATEMENT d /\
     P2_THM_3_28_STATEMENT (:real^3) /\ P2_THM_3_29_STATEMENT (:real^3) /\
     P2C_REQ_CGT_STATEMENT u /\ P2C_REQ_CGT_STATEMENT (:real^3) /\
     CMP_RELVOL_STATEMENT u (:3) /\ CMP_RELVOL_STATEMENT (:real^3) (:3) /\
     P2C_REQ_THM_10_2_VIEW_STATEMENT u /\ P2C_REQ_THM_10_2_VIEW_STATEMENT (:real^3) /\
     P2B_COR_9_95_VIEW_FIX_STATEMENT (:real^3) (:real^3) /\
     P2C_REQ_NONNEG_BOUNDED_FIX_STATEMENT (:real^3) /\
     P2C_REQ_NONNEG_BOUNDED_SLICE_STATEMENT (:real^3) /\
     P2B_REQ_FLAT_FORWARD_STATEMENT (:real^3) /\
     P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT (:real^3) /\ P2B_AVR_ZERO_FIX_STATEMENT (:real^3) /\
     P2C_REQ_LEMMA_11_13_STATEMENT (:real^3) /\ P2C_REQ_TWO_ENDS_NO_CAP_STATEMENT (:real^3) /\
     P2C_REQ_HARNACK_STATEMENT (:real^3) /\ P2C_REQ_DIST_DISTORTION_STATEMENT (:real^3) /\
     P2C_REQ_SCALAR_MIN_STATEMENT (:real^3) /\ P2C_REQ_SMP_POS_STATEMENT (:real^3) /\
     P2C_REQ_SEC_PRESERVED_STATEMENT d /\ P2C_REQ_UNIQ_COMPLETE_STATEMENT (:real^3) /\
     P2C_REQ_BISHOP_GROMOV_STATEMENT (:real^3) /\
     P2C_REQ_SLICE_FIX_STATEMENT u (:real^3) /\ P2C_REQ_SLICE_FIX_STATEMENT u u /\
     P2C_REQ_NECK_FIX_STATEMENT u u /\ P2C_REQ_NECK_FIX_STATEMENT (:real^3) u /\
     P2C_REQ_SLICE_FIX_STATEMENT (:real^3) (:real^3) /\
     P2C_REQ_NECK_FIX_STATEMENT (:real^3) (:real^3) /\
     P2C_REQ_CAP_FIX_STATEMENT u (:real^3) /\ P2C_REQ_SLICE_LOCAL_STATEMENT u u /\
     PDE_CURVATURE_TIME_STATEMENT d (:3) /\ PDE_GLUE_STATEMENT (:real^3) (:3) /\
     APX_NECK_CURV_STATEMENT u /\ APX_A21_STATEMENT u /\ APX_A25_NC_ENDS_STATEMENT u /\
     APX_NO_CAP_IN_NECK_STATEMENT u /\ APX_NO_CAP_IN_NECK_STATEMENT (:real^3) /\
     APX_SEP_OPEN_STATEMENT u /\ APX_SC_SPHERE_SEP_STATEMENT (:real^3) /\
     P2_LEMMA_3_14_STATEMENT (:real^3)
     ==> P2_THM_5_11_STATEMENT u (:real^3) /\ P2C_THM_5_15_STATEMENT u (:real^3) /\
         P2C_LEMMA_11_2_STATEMENT u /\ P2C_THM_11_8_STATEMENT u (:real^3) /\
         P2C_LEMMA_11_23_STATEMENT u /\ P2C_THM_11_19_STATEMENT u /\
         P2C_LEMMA_11_30_STATEMENT u /\ P2C_THM_11_31_STATEMENT u /\
         P2_LEMMA_12_3_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_STD_EXTEND_STATEMENT /\
         P2_PROP_12_7_STATEMENT /\ P2_PROP_12_31_STATEMENT /\ P2C_THM_12_32_STATEMENT /\
         P2_LEMMA_12_37_STATEMENT`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPEC `u:A->bool` P2C_LEMMA_11_2_ROUTE) THEN
  MP_TAC(SPEC `u:A->bool` P2C_THM_11_8_ROUTE) THEN
  REWRITE_TAC[P2C_CG_COMPACT_ROUTE_STATEMENT; P2C_PROP_5_14_ROUTE_STATEMENT;
              P2C_THM_5_11_ROUTE_STATEMENT; P2C_THM_5_15_ROUTE_STATEMENT;
              P2C_HISTORY_REGULAR_ROUTE_STATEMENT; P2C_LEMMA_11_2_ROUTE_STATEMENT;
              P2C_THM_11_1_VIEW_ROUTE_STATEMENT; P2C_THM_11_8_VIEW_ROUTE_STATEMENT;
              P2C_THM_11_8_ROUTE_STATEMENT; P2C_LEMMA_11_21_ROUTE_STATEMENT;
              P2C_LEMMA_11_23_ROUTE_STATEMENT; P2C_LEMMA_11_23_MAXEXT_ROUTE_STATEMENT;
              P2C_LEMMA_11_30_ROUTE_STATEMENT; P2C_THM_11_31_ROUTE_STATEMENT;
              P2C_STD_PARTIAL_EXISTS_ROUTE_STATEMENT; P2C_STD_UNIQUE_ROUTE_STATEMENT;
              P2C_STD_PROPS_ROUTE_STATEMENT] THEN
  REPEAT DISCH_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  P2C_STEP_TAC `P2C_HISTORY_REGULAR_STATEMENT (u:A->bool)` THEN
  P2C_STEP_TAC `P2C_CG_COMPACT_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_CG_COMPACT_STATEMENT (:real^3) (:real^3)` THEN
  P2C_STEP_TAC `P2C_PROP_5_14_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_PROP_5_14_STATEMENT (d:D->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_PROP_5_14_STATEMENT (:real^3) (:real^3)` THEN
  P2C_STEP_TAC `P2_THM_5_11_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_THM_5_15_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_LEMMA_11_2_STATEMENT (u:A->bool)` THEN
  P2C_STEP_TAC `P2C_THM_11_1_VIEW_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_THM_11_1_VIEW_STATEMENT (:real^3) (:real^3)` THEN
  P2C_STEP_TAC `P2C_THM_11_8_VIEW_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_THM_11_8_VIEW_STATEMENT (:real^3) (:real^3)` THEN
  P2C_STEP_TAC `P2C_THM_11_8_STATEMENT (u:A->bool) (:real^3)` THEN
  P2C_STEP_TAC `P2C_LEMMA_11_21_STATEMENT (u:A->bool)` THEN
  P2C_STEP_TAC `P2C_LEMMA_11_23_STATEMENT (u:A->bool)` THEN
  P2C_STEP_TAC `P2C_LEMMA_11_23_MAXEXT_STATEMENT (u:A->bool)` THEN
  SUBGOAL_THEN `P2C_THM_11_19_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2C_THM_11_19_FROM_PARTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  P2C_STEP_TAC `P2C_LEMMA_11_30_STATEMENT (u:A->bool)` THEN
  P2C_STEP_TAC `P2C_THM_11_31_STATEMENT (u:A->bool)` THEN
  P2C_STEP_TAC `P2C_STD_PARTIAL_EXISTS_STATEMENT` THEN
  P2C_STEP_TAC `P2C_STD_UNIQUE_STATEMENT` THEN
  P2C_STEP_TAC `P2C_STD_PROPS_STATEMENT` THEN
  MP_TAC P2C_STD_ASSEMBLY THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

