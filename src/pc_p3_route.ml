(* ========================================================================= *)
(* Unit pc_p3_route: the further MT Ch 13-17 results of the route as         *)
(* statement constants (R1-R14: Thm 13.2, Lemma 14.11, Props 15.2, 16.3,     *)
(* 16.4, 16.5, 16.13, Lemma 16.15, Prop 16.21, Cor 16.24, Lemmas 17.2 and    *)
(* 17.7, and the curvature bounds R13, R14) and the route obligations with   *)
(* P3_FULL_CHAIN.  Thm 13.2 has the collapse clause F2 and (A0 + 4) d0 < 1;  *)
(* Props 16.4, 16.5, 16.13, 16.21, Lemma 16.15 and Cor 16.24 have            *)
(* existential eps thresholds (they rest on the corrected Lemma 11.2, which  *)
(* needs eps <= eps0; C >= 2 comes from the monotonicity of canonical        *)
(* neighbourhoods in C).  R13 and R14 supply the scale-invariant C^2         *)
(* curvature bound on the source neighbourhoods of the corrected slice form  *)
(* of MT Prop 9.79.                                                          *)
(* ========================================================================= *)

needs "src/pc_p3_assembly.ml";;
needs "src/pc_p3_iface.ml";;
needs "src/pc_rfs_assembly.ml";;
needs "src/pc_p3_s16sst.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* R1. MT Thm 13.2 with Claim 13.1 (pp. 332-333), in model coordinates: the *)
(* neck metric gN on the annulus (delta-close to the cylinder after scaling  *)
(* by h^-2, h <= h0 = R0^(-1/2), pinched at time t) is capped by a metric gS *)
(* on the model domain s1 > -1/delta, equal to gN (through p3_std_nc) where  *)
(* s1 < 0, pinched at time t (item 1), positively curved where s1 >= 1      *)
(* (item 2), with a smooth radial collapse xi of pointwise norm <= 1 from   *)
(* gN to gS (item 3 smoothed: MT's xi has a kink at                         *)
(* s = A0 + 4), inverse to p3_std_nc where s <= 0, into the closed cap      *)
(* s1 >= 0 where s >= 0 (F2), and h^-2 gS                                   *)
(* dd-close to g0 on B(0,1/dd) when delta <= md dd (item 4).  d0 is small   *)
(* enough that the model domain reaches s1 = A0 + 4: (A0 + 4) d0 < 1 (F3).  *)
(* MT Sec 13.3.2 has a gap; the proof here is the Part 3 proof.             *)
(* ------------------------------------------------------------------------- *)

let P3_THM_13_2_STATEMENT = new_definition
 `P3_THM_13_2_STATEMENT <=>
    !g0 A0. p3_std_initial g0 A0
      ==> ?d0 h0 md. &0 < d0 /\ (A0 + &4) * d0 < &1 /\ &0 < h0 /\ p3_modulus md /\
            !dl h t gN.
               &0 < dl /\ dl <= d0 /\ &0 < h /\ h <= h0 /\ &0 <= t /\
               riemannian_metric (open_set_atlas (rfs_neck_dom dl)) gN /\
               rfs_close_on (rfs_kreg dl) dl (rfs_neck_dom dl) (cylinder_flow (&0))
                            (\y. inv(h pow 2) %% gN y) /\
               (!y. y IN rfs_neck_dom dl
                    ==> rfs_pinched_at (open_set_atlas (rfs_neck_dom dl)) gN t y)
               ==> ?gS xi.
                     riemannian_metric
                       (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z}) gS /\
                     (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x /\
                          A0 + &4 - p3_std_dist g0 x < &0
                          ==> gS x = mpullback (p3_std_nc g0 A0) gN x) /\
                     (!x. --(inv dl) < A0 + &4 - p3_std_dist g0 x
                          ==> rfs_pinched_at
                                (open_set_atlas {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                                gS t x) /\
                     (!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
                              ==> &0 < mfd_sectional
                                         (open_set_atlas
                                            {z | --(inv dl) < A0 + &4 - p3_std_dist g0 z})
                                         gS x u v) /\
                     (!dd. &0 < dd /\ dl <= md dd
                           ==> rfs_close_on (rfs_kreg dd) dd
                                 {x | p3_std_dist g0 x < inv dd /\
                                      --(inv dl) < A0 + &4 - p3_std_dist g0 x}
                                 g0 (\x. inv(h pow 2) %% gS x)) /\
                     smooth_map_on (rfs_neck_dom dl) (xi:real^3->real^3) /\
                     (!y. y IN rfs_neck_dom dl
                          ==> --(inv dl) < A0 + &4 - p3_std_dist g0 (xi y) /\
                              (sqrt(&2) * log(norm y) <= &0 ==> p3_std_nc g0 A0 (xi y) = y) /\
                              (&0 <= sqrt(&2) * log(norm y)
                               ==> &0 <= A0 + &4 - p3_std_dist g0 (xi y)) /\
                              (A0 + &4 <= sqrt(&2) * log(norm y) ==> xi y = vec 0)) /\
                     (!y v. y IN rfs_neck_dom dl
                            ==> (jacobian xi (at y) ** v) dot
                                (gS (xi y) ** (jacobian xi (at y) ** v)) <=
                                v dot (gN y ** v))`;;

(* ------------------------------------------------------------------------- *)
(* R2. MT Lemma 14.11 (pp. 349-350) in the form the analysis uses: on an    *)
(* open set W of retained points of event k the family of the history is a  *)
(* smooth Ricci flow across the event time (Prop 3.12; retained points       *)
(* carry the limit metric, rfs_event_ok).  With the slab flows this makes   *)
(* every persisting region a Ricci flow (MT Prop 14.12).                    *)
(* ------------------------------------------------------------------------- *)

let P3_LEMMA_14_11_STATEMENT = new_definition
 `P3_LEMMA_14_11_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) k W a b.
       rfs_history_ok hs /\ 1 <= k /\ k <= hs_count hs /\
       open_in (hs_top hs k) W /\ W SUBSET topspace(hs_top hs (k - 1)) /\
       hs_time hs (k - 1) <= a /\ a < hs_time hs k /\
       hs_time hs k < b /\ b < hs_time hs (k + 1)
       ==> p3_region_flow hs W a b`;;

(* ------------------------------------------------------------------------- *)
(* R3. MT Prop 15.2 (p. 353): gluing an evolving beta eps-neck on            *)
(* (t - t0/R, t] with a strong (beta eps/2)-neck at the earlier time gives a *)
(* strong eps-neck at (x,t); the containment of images is the isometric    *)
(* embedding of the slices (points are fixed along flow lines).  Used in    *)
(* Lemma 17.7 (p. 406).                                                      *)
(* The statement is for the view of a valid history, not for an arbitrary    *)
(* view: a view has no consistency between the structures at different       *)
(* times, and for arbitrary views the statement is false (a slice structure  *)
(* transported by a point swap).  beta depends on eps: MT's compactness      *)
(* proof only works for fixed eps, and its only use, Lemma 17.7, fixes eps   *)
(* before beta.                                                              *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_15_2_STATEMENT = new_definition
 `P3_PROP_15_2_STATEMENT (u:A->bool) <=>
    !eps. &0 < eps /\ eps < &1
      ==> ?beta. &0 < beta /\ beta < &1 / &2 /\
            !(hs:(A)rfs_history) x t t0 e e'.
               rfs_history_ok hs /\
               rfs_evolving_neck (rfs_view hs) (beta * eps) x t t0 e /\
               rfs_strong_neck (rfs_view hs) (beta * eps / &2) x
                               (t - t0 / rfs_vscalar (rfs_view hs) t x) e' /\
               IMAGE e (rfs_neck_dom (beta * eps)) SUBSET IMAGE e' (rfs_neck_dom (beta * eps / &2))
               ==> ?e''. rfs_strong_neck (rfs_view hs) eps x t e''`;;

(* ------------------------------------------------------------------------- *)
(* R4. MT Prop 16.3 (p. 368): at a point with a strong (C,eps)-canonical    *)
(* neighbourhood, Vol B(x,t,R^(-1/2)) >= kappa(C) R^(-3/2) or x lies in a   *)
(* positively curved component.  The slice is a compact smooth Riemannian    *)
(* manifold (otherwise mfd_dist and the ball volume can be junk or infinite; *)
(* rfs_view hs at live times has it); the canonical neighbourhoods carry the *)
(* volume clause on C-components (p3_canonv_at, KL Def 69.1), the slices are *)
(* Hausdorff with simply connected components (eps-round components are then *)
(* round S^3: Killing-Hopf), and there is no positive-curvature exemption.   *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_16_3_STATEMENT = new_definition
 `P3_PROP_16_3_STATEMENT (u:A->bool) <=>
    ?eps3. &0 < eps3 /\
      !C. &1 < C
        ==> ?kappa. &0 < kappa /\
              !eps V x t.
                 &0 < eps /\ eps <= eps3 /\ hausdorff_space (rfs_vtop V t) /\
                 smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
                 riemannian_metric (rfs_vatlas V t) (rfs_vmetric V t) /\
                 compact_space (rfs_vtop V t) /\ rfs_components_sc (rfs_vtop V t) /\
                 p3_canonv_at (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) C eps x t /\
                 &0 < rfs_vscalar V t x
                 ==> ?v. mfd_has_volume (rfs_vtop V t,rfs_vatlas V t) (rfs_vmetric V t)
                           (rfs_vball V t x (inv(sqrt(rfs_vscalar V t x)))) v /\
                         kappa * inv(sqrt(rfs_vscalar V t x)) pow 3 <= v`;;

(* ------------------------------------------------------------------------- *)
(* R5. MT Prop 16.4 (p. 369; eps <= eps164): in the setting of Prop 16.1 at  *)
(* step i (new parameter r', control <= dlt(r') on I_i and I_(i+1)), a point *)
(* x at time tt in [T_i, horizon) with P(x,tt,r,-r^2) existing and abs       *)
(* Rm <= r^-2, r >= r', has an open U in the smooth part over [T_(i-1), tt)  *)
(* with (1) minimizing L-geodesics from x to all its points, (2) non-empty   *)
(* slices, (3) slice minima of L attained and <= 3 sqrt(tt - t), (4) compact *)
(* sets of slice minimizers over compact time intervals.  Item (3) is the    *)
(* corrected Cor 7.12, whose added hypothesis (lower semicontinuity of the   *)
(* slice minimum of l_x) Part 3 proves for U as in MT Claim 16.25.  The      *)
(* parabolic scale bound is a second scale rr <= r' (r >= rr), separate from *)
(* the canonical parameter r' (KL Lemma 79.3); dlt may depend on rr.         *)
(* Prop 16.1 needs it at rr = r'/100 (KL Sublemma 79.23).                    *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_16_4_STATEMENT = new_definition
 `P3_PROP_16_4_STATEMENT (u:A->bool) <=>
    ?eps164. &0 < eps164 /\
    !C eps hf md g0 A0.
       &1 < C /\ &0 < eps /\ eps <= eps164 /\
       p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
       ==> !i rs ks ds r' rr.
             1 <= i /\ rs 0 = eps /\
             p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
             &0 < r' /\ r' <= rs i /\ &0 < rr /\ rr <= r'
             ==> ?dlt. &0 < dlt /\
                   !rs' ks' dd (hs:(A)rfs_history) x tt r.
                      p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\
                      p3_T i <= tt /\ tt < rfs_horizon hs /\ x IN topspace(rfs_top_at hs tt) /\
                      rr <= r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
                      (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
                             ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2))
                      ==> ?U. p3_st_open hs U (p3_T (i - 1)) tt /\
                              (!t y. y IN U t
                                     ==> ?gamma. rfs_min_Lgeod hs tt x (tt - t) gamma /\
                                                 gamma (tt - t) = y) /\
                              (!t. p3_T (i - 1) <= t /\ t < tt ==> ~(U t = {})) /\
                              (!t. p3_T (i - 1) <= t /\ t < tt
                                   ==> ?y. y IN p3_Lmin_set hs tt x U t /\
                                           rfs_Lx hs tt x (tt - t) y <= &3 * sqrt(tt - t)) /\
                              (!a b. p3_T (i - 1) <= a /\ a <= b /\ b < tt
                                     ==> p3_st_compact hs
                                           (\t. if a <= t /\ t <= b
                                                then p3_Lmin_set hs tt x U t else {}))`;;

(* ------------------------------------------------------------------------- *)
(* R6. MT Prop 16.5 (p. 370; eps <= eps165): evolution of surgery caps.      *)
(* Given r (the canonical neighbourhood parameter), A, a closeness dd2 and   *)
(* theta < 1, for surgery control <= d0 the rescaled (h^-2, shifted) flow on *)
(* the image by the cap coordinates Phi of B_g0(0,A) stays dd2-close to A    *)
(* standard flow G for normalized times < theta (up to the horizon), or the  *)
(* whole ball disappears at a later event k' before ts + theta h^2.  G is    *)
(* existential: uniqueness of the standard solution is avoided (Lemma 16.8   *)
(* gets a limit that is a partial standard flow, extended by P2_STD_EXTEND). *)
(* Lemma 16.8 uses P2C_PROP_5_14 (the limit keeps the cap maps and the       *)
(* initial slice g0; histories are regular views by P2C_HISTORY_REGULAR);    *)
(* the derivative bounds at time 0 come from the closeness clause of         *)
(* p3_cap_param, completeness on [0,T'] from the curvature bound of the      *)
(* standard flow, uniform in A.  The hypothesis rp ts <= eps (MT:            *)
(* r(t) <= r_0 = eps) makes the surgery scale h <= dl^2 eps, so h/r -> 0 as  *)
(* dl -> 0; without it Lemma 11.2 gives no uniform curvature control near    *)
(* the cap.  Same for Prop 16.13.  A cutoff time tc <= rfs_horizon hs: the   *)
(* canonical neighbourhood assumption is needed only before tc, the          *)
(* closeness holds also at times <= tc, and the disappearance alternative    *)
(* also covers an event at time tc.  Lemma 17.2, case (ii), needs the cap at *)
(* the first bad time ts itself, which may be an event time (MT Claim 17.3,  *)
(* p. 399, uses Prop 16.5 past ts).  The choice tc = rfs_horizon hs gives    *)
(* MT's form.                                                                *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_16_5_STATEMENT = new_definition
 `P3_PROP_16_5_STATEMENT (u:A->bool) <=>
    ?eps165. &0 < eps165 /\
    !C eps hf md g0 A0 r A dd2 theta.
       &1 < C /\ &0 < eps /\ eps <= eps165 /\
       p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
       &0 < r /\ &0 < A /\ &0 < dd2 /\ &0 < theta /\ theta < &1
       ==> ?d0. &0 < d0 /\
             !rp dl (hs:(A)rfs_history) k i Phi xi ts h tc.
                p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ tc <= rfs_horizon hs /\
                (!t x. &0 <= t /\ t < tc /\ x IN topspace(rfs_top_at hs t) /\
                       inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                       ==> p3_canon_at (rfs_view hs) C eps x t) /\
                1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                ts = hs_time hs k /\ ts < tc /\ h = p3_hscale hf rp dl ts /\
                p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                dl ts <= d0 /\ rp ts <= eps
                ==> ?G. p3_std_flow g0 (&1) G /\
                    (p3_view_close
                      (rfs_flow_view (euclidean,open_set_atlas (:real^3)) {s | &0 <= s /\ s < &1} G)
                      (&0) (&1) {x | p3_std_dist g0 x < A}
                      (rfs_view hs) ts (inv(h pow 2)) Phi
                      {s | &0 <= s /\ s < theta /\ ts + s * h pow 2 <= tc /\
                           ts + s * h pow 2 < rfs_horizon hs} dd2 \/
                    ?k'. k < k' /\ k' <= hs_count hs /\ hs_time hs k' <= tc /\
                         hs_time hs k' < ts + theta * h pow 2 /\
                         p3_view_close
                           (rfs_flow_view (euclidean,open_set_atlas (:real^3))
                                          {s | &0 <= s /\ s < &1} G)
                           (&0) (&1) {x | p3_std_dist g0 x < A}
                           (rfs_view hs) ts (inv(h pow 2)) Phi
                           {s | &0 <= s /\ ts + s * h pow 2 < hs_time hs k'} dd2 /\
                         DISJOINT (IMAGE Phi {x | p3_std_dist g0 x < A}) (topspace(hs_top hs k')))`;;

(* ------------------------------------------------------------------------- *)
(* R7. MT Prop 16.13 (p. 376; eps <= eps1613): backward-time curves inside   *)
(* the evolving cap region that come from its top (time ts + theta0 h^2) or  *)
(* its side (distance A) and reach B(0,A/2) at a time tp in [ts, ts + h^2/2] *)
(* have energy (integral of R + |X|^2) > ell.  Model balls through Phi stand *)
(* for the history balls B(p,ts,A h) (the metrics are close by Prop 16.5).   *)
(* The energy integrand is assumed integrable (a real_integral of a          *)
(* non-integrable function is one fixed unknown value, so without it the     *)
(* statement is unprovable).  The curve starts at any time                   *)
(* Tp <= ts + theta0 h^2 (top: Tp = ts + theta0 h^2; side: gamma 0 at        *)
(* distance A), as used on p. 382 for side entries (with Tp = min(T,         *)
(* ts + theta0 h^2) the side case would be vacuous: the slice at the horizon *)
(* is empty).  1/2 <= theta0 (MT p. 377 takes theta0 close to 1; Lemma 16.15 *)
(* part (2), MT p. 381, needs t + h^2/2 <= t + theta0 h^2).                  *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_16_13_STATEMENT = new_definition
 `P3_PROP_16_13_STATEMENT (u:A->bool) <=>
    ?eps1613. &0 < eps1613 /\
    !C eps hf md g0 A0 r ell.
       &1 < C /\ &0 < eps /\ eps <= eps1613 /\
       p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
       &0 < r /\ &0 < ell
       ==> ?A1 theta0. &0 < A1 /\ &0 < theta0 /\ &1 / &2 <= theta0 /\ theta0 < &1 /\
             !A. A1 <= A
               ==> ?d0. &0 < d0 /\
                     !rp dl (hs:(A)rfs_history) k i Phi xi ts h Tp tp gamma.
                        p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                        (!t x. &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                               inv(r pow 2) <= rfs_vscalar (rfs_view hs) t x
                               ==> p3_canon_at (rfs_view hs) C eps x t) /\
                        1 <= k /\ k <= hs_count hs /\ i IN ev_index(hs_event hs k) /\
                        ts = hs_time hs k /\ h = p3_hscale hf rp dl ts /\
                        p3_cap_param (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i Phi xi /\
                        dl ts <= d0 /\ rp ts <= eps /\
                        Tp <= ts + theta0 * h pow 2 /\
                        (!s. ts <= s /\ s <= Tp
                             ==> IMAGE Phi {x | p3_std_dist g0 x <= A} SUBSET
                                 topspace(rfs_top_at hs s)) /\
                        ts <= tp /\ tp <= ts + h pow 2 / &2 /\ tp <= Tp /\
                        rfs_st_curve hs Tp gamma (&0) (Tp - tp) /\
                        (!tau. &0 <= tau /\ tau <= Tp - tp
                               ==> gamma tau IN IMAGE Phi {x | p3_std_dist g0 x <= A}) /\
                        (Tp = ts + theta0 * h pow 2 \/
                         gamma (&0) IN IMAGE Phi {x | p3_std_dist g0 x = A}) /\
                        gamma (Tp - tp) IN IMAGE Phi {x | p3_std_dist g0 x < A / &2} /\
                        (\tau. mfd_scalar (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                                          (gamma tau) +
                               mfd_speed (rfs_atlas_at hs (Tp - tau)) (rfs_metric_at hs (Tp - tau))
                                         gamma (&0) (Tp - tp) tau pow 2)
                        real_integrable_on real_interval[&0,Tp - tp]
                        ==> ell < p3_energy hs Tp gamma (Tp - tp)`;;

(* ------------------------------------------------------------------------- *)
(* R8. MT Lemma 16.15 (p. 379; eps <= eps1615): in the setting of Prop 16.4, *)
(* for L0 there are dlt and taup (depending on L0 and r') such that curves   *)
(* from x with L_plus < L0 stay in P(x,tt,r/2,-r^2) for tau <= taup and miss *)
(* the evolving (50 + A0)-balls of the surgery caps for h^2/2 after each     *)
(* surgery.  The L_plus integrand is assumed integrable (otherwise p3_Lplus  *)
(* is one fixed unknown value and the statement is false for wild curves).   *)
(* Part (2) holds for every surgery time in [T(i-1),tt), not only those      *)
(* after the end time tt - tau0 of the curve (MT Claim 16.22 is used for     *)
(* curves ending in (t,t + h^2/2), p. 385-387).  The parabolic scale bound   *)
(* is a second scale rr <= r' (r >= rr), separate from the canonical         *)
(* parameter r' (KL Lemma 79.3); dlt may depend on rr.  Prop 16.1 needs it   *)
(* at rr = r'/100 (KL Sublemma 79.23).                                       *)
(* ------------------------------------------------------------------------- *)

let P3_LEMMA_16_15_STATEMENT = new_definition
 `P3_LEMMA_16_15_STATEMENT (u:A->bool) <=>
    ?eps1615. &0 < eps1615 /\
    !C eps hf md g0 A0.
       &1 < C /\ &0 < eps /\ eps <= eps1615 /\
       p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
       ==> !i rs ks ds r' rr L0.
             1 <= i /\ rs 0 = eps /\
             p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
             &0 < r' /\ r' <= rs i /\ &0 < rr /\ rr <= r' /\ &0 < L0
             ==> ?dlt taup. &0 < dlt /\ &0 < taup /\
                   !rs' ks' dd (hs:(A)rfs_history) x tt r tau0 gamma.
                      p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\
                      p3_T i <= tt /\ tt < rfs_horizon hs /\ x IN topspace(rfs_top_at hs tt) /\
                      rr <= r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
                      (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
                             ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
                      &0 < tau0 /\ tau0 <= tt - p3_T (i - 1) /\
                      rfs_st_curve hs tt gamma (&0) tau0 /\ gamma (&0) = x /\
                      (\tau. sqrt tau *
                             (max (&0) (mfd_scalar (rfs_atlas_at hs (tt - tau))
                                                   (rfs_metric_at hs (tt - tau)) (gamma tau)) +
                              mfd_speed (rfs_atlas_at hs (tt - tau)) (rfs_metric_at hs (tt - tau))
                                        gamma (&0) tau0 tau pow 2))
                      real_integrable_on real_interval[&0,tau0] /\
                      p3_Lplus hs tt gamma tau0 < L0
                      ==> (!tau. &0 <= tau /\ tau <= min taup tau0
                                 ==> gamma tau IN rfs_vball (rfs_view hs) tt x (r / &2)) /\
                          (!k j Phi xi tp.
                              1 <= k /\ k <= hs_count hs /\ j IN ev_index(hs_event hs k) /\
                              p3_T (i - 1) <= hs_time hs k /\ hs_time hs k < tt /\
                              p3_cap_param (md,g0,A0) (p3_stepf dd,p3_hscale hf (p3_stepf rs') (p3_stepf dd))
                                           hs k j Phi xi /\
                              hs_time hs k <= tp /\
                              tp <= hs_time hs k +
                                    p3_hscale hf (p3_stepf rs') (p3_stepf dd) (hs_time hs k) pow 2 / &2 /\
                              (!s. hs_time hs k <= s /\ s <= tp
                                   ==> IMAGE Phi {z | p3_std_dist g0 z < A0 + &50} SUBSET
                                       topspace(rfs_top_at hs s))
                              ==> !tau. &0 <= tau /\ tau <= tau0 /\
                                        hs_time hs k <= tt - tau /\ tt - tau <= tp
                                        ==> ~(gamma tau IN IMAGE Phi {z | p3_std_dist g0 z < A0 + &50}))`;;

(* ------------------------------------------------------------------------- *)
(* R9. MT Prop 16.21(3) (p. 385; with Def 16.20; eps <= eps1621): in the     *)
(* setting of Prop 16.4, for every bound Lb there is a compact subset        *)
(* K = Y(ell) of the smooth part containing every admissible curve from x of *)
(* L-length <= Lb back to T_(i-1).  Items (1)-(2) then follow from the       *)
(* corrected P2_LEMMA_7_2 in K: minimizers as limits of minimizing           *)
(* sequences, and lower semicontinuity of L in competitor form (the limit    *)
(* curve itself need not be admissible).  MT's proof needs care at the       *)
(* compactness of Y(ell) and the choice of the Delta t_j.  The parabolic     *)
(* scale bound is a second scale rr <= r' (r >= rr), separate from the       *)
(* canonical parameter r' (KL Lemma 79.3); dlt may depend on rr.  Prop 16.1  *)
(* needs it at rr = r'/100 (KL Sublemma 79.23).                              *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_16_21_STATEMENT = new_definition
 `P3_PROP_16_21_STATEMENT (u:A->bool) <=>
    ?eps1621. &0 < eps1621 /\
    !C eps hf md g0 A0.
       &1 < C /\ &0 < eps /\ eps <= eps1621 /\
       p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
       ==> !i rs ks ds r' rr Lb.
             1 <= i /\ rs 0 = eps /\
             p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
             &0 < r' /\ r' <= rs i /\ &0 < rr /\ rr <= r' /\ &0 < Lb
             ==> ?dlt. &0 < dlt /\
                   !rs' ks' dd (hs:(A)rfs_history) x tt r.
                      p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\
                      p3_T i <= tt /\ tt < rfs_horizon hs /\ x IN topspace(rfs_top_at hs tt) /\
                      rr <= r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
                      (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
                             ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2))
                      ==> ?K. p3_st_compact hs K /\
                              !tau0 gamma.
                                 &0 < tau0 /\ tau0 <= tt - p3_T (i - 1) /\
                                 rfs_L_adm hs tt x tau0 gamma /\
                                 rfs_L_length hs tt gamma tau0 <= Lb
                                 ==> !tau. &0 < tau /\ tau <= tau0 ==> gamma tau IN K (tt - tau)`;;

(* ------------------------------------------------------------------------- *)
(* R10. MT Cor 16.24 (p. 388; eps <= eps1624): in the same setting, a curve  *)
(* of L-length <= Lb from x to y gives a minimizing L-geodesic from x to y   *)
(* in the smooth part.  The parabolic scale bound is a second scale rr <= r' *)
(* (r >= rr), separate from the canonical parameter r' (KL Lemma 79.3); dlt  *)
(* may depend on rr.  Prop 16.1 needs it at rr = r'/100 (KL Sublemma 79.23). *)
(* ------------------------------------------------------------------------- *)

let P3_COR_16_24_STATEMENT = new_definition
 `P3_COR_16_24_STATEMENT (u:A->bool) <=>
    ?eps1624. &0 < eps1624 /\
    !C eps hf md g0 A0.
       &1 < C /\ &0 < eps /\ eps <= eps1624 /\
       p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
       ==> !i rs ks ds r' rr Lb.
             1 <= i /\ rs 0 = eps /\
             p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
             &0 < r' /\ r' <= rs i /\ &0 < rr /\ rr <= r' /\ &0 < Lb
             ==> ?dlt. &0 < dlt /\
                   !rs' ks' dd (hs:(A)rfs_history) x tt r tau0 gamma.
                      p3_p16_setting (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dlt (rs',ks',dd) hs /\
                      p3_T i <= tt /\ tt < rfs_horizon hs /\ x IN topspace(rfs_top_at hs tt) /\
                      rr <= r /\ rfs_parabolic_exists (rfs_view hs) tt x r (r pow 2) /\
                      (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball (rfs_view hs) tt x r
                             ==> p3_vrm (rfs_view hs) s y <= inv(r pow 2)) /\
                      &0 < tau0 /\ tau0 <= tt - p3_T (i - 1) /\
                      rfs_L_adm hs tt x tau0 gamma /\ rfs_L_length hs tt gamma tau0 <= Lb
                      ==> ?gamma'. rfs_min_Lgeod hs tt x tau0 gamma' /\
                                   gamma' tau0 = gamma tau0`;;

(* ------------------------------------------------------------------------- *)
(* R11. MT Lemma 17.2 (p. 395): if a history in the setting of Prop 17.1     *)
(* with new parameter r' and control <= dlt(r') fails the strong canonical  *)
(* neighbourhood assumption, there is a first bad time ts in [T_i, horizon): *)
(* the truncation at ts satisfies it and some x at time ts with             *)
(* R >= r'^-2 has no strong (C,eps)-canonical neighbourhood.                *)
(* g0, A0 are quantified before C172.                                       *)
(* ------------------------------------------------------------------------- *)

(* The statement uses canonv neighbourhoods (p3_canonv_at /                  *)
(* p3_canonv_assumption: the C-component alternative carries the volume      *)
(* clause p3_comp_vol, KL 69.1 (c)).                                         *)

let P3_LEMMA_17_2_STATEMENT = new_definition
 `P3_LEMMA_17_2_STATEMENT (u:A->bool) <=>
    ?eps172. &0 < eps172 /\
      !eps g0 A0. &0 < eps /\ eps <= eps172 /\ p3_std_initial g0 A0
        ==> ?C172. &1 < C172 /\
              !C hf md.
                 C172 <= C /\ p3_hfun C hf /\ p3_modulus md
                 ==> !i rs ks ds r'.
                       1 <= i /\ rs 0 = eps /\
                       p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
                       &0 < r' /\ r' <= rs i
                       ==> ?dlt. &0 < dlt /\
                             !rs' ks' dd (hs:(A)rfs_history).
                                rs' (SUC i) = r' /\
                                p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
                                ~p3_canonv_assumption (rfs_view hs) C eps (p3_stepf rs')
                                ==> ?ts x. p3_T i <= ts /\ ts < rfs_horizon hs /\
                                           p3_canonv_assumption (rfs_trunc (rfs_view hs) ts)
                                             C eps (p3_stepf rs') /\
                                           x IN topspace(rfs_top_at hs ts) /\
                                           inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                                           ~p3_canonv_at (rfs_view hs) C eps x ts`;;

(* ------------------------------------------------------------------------- *)
(* R12. MT Lemma 17.7 (p. 403), sequence-free: for A', D', t' there is      *)
(* rstar, and for r' <= rstar a control bound dlt(r'), such that, at a      *)
(* first bad time ts (truncation canonical), a point x with                 *)
(* R(x) = Q >= r'^-2 is not a counterexample if some y in B(x,ts,A' Q^(-1/2)) *)
(* lies in the closed core of a surgery cap created at time >= ts - t'/Q    *)
(* and the curvature along its flow line up to ts is <= D' Q.  (MT: the     *)
(* backward flow line from y ends in a cap.)                                *)
(* g0, A0 are quantified before C177, dlt after r'.  The event time is       *)
(* strictly before ts: at hs_time hs k = ts the normalized time in the       *)
(* standard solution is 0, where the formal Thm 12.32 (t > 0) does not       *)
(* apply; MT treats caps at the bad time itself separately (Claim 17.6 with  *)
(* Thm 13.2), and so does Prop 17.1.                                         *)
(* ------------------------------------------------------------------------- *)

(* The truncation satisfies the canonv assumption and x gets a canonv        *)
(* neighbourhood.                                                            *)

let P3_LEMMA_17_7_STATEMENT = new_definition
 `P3_LEMMA_17_7_STATEMENT (u:A->bool) <=>
    ?eps177. &0 < eps177 /\
      !eps g0 A0. &0 < eps /\ eps <= eps177 /\ p3_std_initial g0 A0
        ==> ?C177. &1 < C177 /\
              !C hf md.
                 C177 <= C /\ p3_hfun C hf /\ p3_modulus md
                 ==> !i rs ks ds Ap Dp tp.
                       1 <= i /\ rs 0 = eps /\
                       p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
                       &0 < Ap /\ &0 < Dp /\ &0 < tp
                       ==> ?rstar. &0 < rstar /\
                             !r'. &0 < r' /\ r' <= rstar /\ r' <= rs i
                               ==> ?dlt. &0 < dlt /\
                                     !rs' ks' dd (hs:(A)rfs_history) ts x y k j.
                                        rs' (SUC i) = r' /\
                                        p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt
                                                    (rs',ks',dd) hs /\
                                        p3_T i <= ts /\ ts < rfs_horizon hs /\
                                        p3_canonv_assumption (rfs_trunc (rfs_view hs) ts)
                                                                 C eps (p3_stepf rs') /\
                                        x IN topspace(rfs_top_at hs ts) /\
                                        inv(r' pow 2) <= rfs_vscalar (rfs_view hs) ts x /\
                                        y IN rfs_vball (rfs_view hs) ts x
                                               (Ap * inv(sqrt(rfs_vscalar (rfs_view hs) ts x))) /\
                                        1 <= k /\ k <= hs_count hs /\
                                        j IN ev_index(hs_event hs k) /\
                                        ts - tp * inv(rfs_vscalar (rfs_view hs) ts x) <=
                                        hs_time hs k /\
                                        hs_time hs k < ts /\
                                        y IN IMAGE (ev_capm (hs_event hs k) j) (cball(vec 0,&1)) /\
                                        p3_flowline hs y (hs_time hs k) ts /\
                                        (!s. hs_time hs k <= s /\ s <= ts
                                             ==> rfs_vscalar (rfs_view hs) s y <=
                                                 Dp * rfs_vscalar (rfs_view hs) ts x)
                                        ==> p3_canonv_at (rfs_view hs) C eps x ts`;;

(* ------------------------------------------------------------------------- *)
(* R13.  The C^2 curvature bound of the corrected P2_PROP_9_79_SLICE for a   *)
(* history slice as the source: at a point x with R(x) >= rp^-2 and a        *)
(* (C,eps)-canonical neighbourhood U at time t, in a structurally controlled *)
(* history with small control and the canonical neighbourhood assumption     *)
(* before t, the normalized metric R(x) g(t) has lrm_deriv_norm2 l <= Kr on  *)
(* U for l <= 2 (exactly the clause of P2B_PROP_9_79_SLICE_FIX).  Proved as  *)
(* RFA_P3_HIST_C2_BOUND (units pc_rfa_histc2a, pc_rfa_histc2b,               *)
(* pc_rfa_histc2c): closeness to the model metrics on necks and round        *)
(* components, Shi's local estimates (P2_THM_3_28) on the cores of caps and  *)
(* on C-components, and near new caps, where backward parabolic              *)
(* neighbourhoods do not exist, the cap closeness of p3_cap_param with Shi's *)
(* estimate from initial data (the cap clauses alone bound neither Rm nor    *)
(* its derivatives).  Needed in Lemma 17.2 (SLICE u u) and Prop 17.1 (SLICE  *)
(* u w).  Kr comes first, then a lower bound r0 <= rp t and d0 depending on  *)
(* r0; the control dl <= d0 and rp <= eps are needed only on the window      *)
(* [t - 1/32, t], which the uses at t >= p3_T i (i >= 1) have, since p3_T    *)
(* i - p3_T (i - 1) >= 1/32 and steps i, SUC i are controlled.  eps0 comes   *)
(* before C (Kr may depend on C): the uses apply the bound to canonical      *)
(* neighbourhoods whose C depends on eps (the cap constant of Thm 12.32 in   *)
(* Lemma 17.2, case (ii), and C >= C17(eps) in Prop 17.1), so eps <= eps0(C) *)
(* could not be arranged with eps0 depending on C.                           *)
(* ------------------------------------------------------------------------- *)

let P3_HIST_C2_BOUND_STATEMENT = new_definition
 `P3_HIST_C2_BOUND_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
            !C eps hf md g0 A0.
               &1 < C /\ &0 < eps /\ eps <= eps0 /\ p3_hfun C hf /\ p3_modulus md /\
               p3_std_initial g0 A0
               ==> ?Kr. &0 < Kr /\
                     !r0. &0 < r0
                       ==> ?d0. &0 < d0 /\
                             !rp dl (hs:(A)rfs_history) t x U.
                                p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                                r0 <= rp t /\
                                (!s. &0 <= s /\ t - &1 / &32 <= s /\ s <= t
                                     ==> rp s <= eps /\ dl s <= d0) /\
                                rfs_canonical_assumption (rfs_trunc (rfs_view hs) t) C eps rp /\
                                &0 <= t /\ t < rfs_horizon hs /\ x IN topspace(rfs_top_at hs t) /\
                                inv(rp t pow 2) <=
                                mfd_scalar (rfs_atlas_at hs t) (rfs_metric_at hs t) x /\
                                rfs_canonical_nbhd (rfs_top_at hs t,rfs_atlas_at hs t)
                                                   (rfs_metric_at hs t) C eps x U
                                ==> !y l. y IN U /\ l <= 2
                                          ==> lrm_deriv_norm2 l
                                                (metric_local (rfs_atlas_at hs t)
                                                   (chart_at (rfs_atlas_at hs t) y)
                                                   (\z. mfd_scalar (rfs_atlas_at hs t)
                                                          (rfs_metric_at hs t) x %%
                                                        rfs_metric_at hs t z))
                                                (SND(chart_at (rfs_atlas_at hs t) y) y) <= Kr`;;

(* ------------------------------------------------------------------------- *)
(* R14.  The same bound for a slice of a standard flow as the source (Lemmas *)
(* 17.2, 17.7 and Prop 17.1, SLICE (:real^3) u), for 0 <= t < 1 (at t = 0    *)
(* the slice is g0), uniform over all standard flows: the standard solution  *)
(* has bounded geometry at each time and derivative estimates scaled by R    *)
(* where R is large (MT Ch 12); proved as RFA_P3_STD_C2_BOUND (unit          *)
(* pc_rfa_stdc2).  eps0 comes before C (Kr may depend on C), for the same    *)
(* reason as in R13.                                                         *)
(* ------------------------------------------------------------------------- *)

let P3_STD_C2_BOUND_STATEMENT = new_definition
 `P3_STD_C2_BOUND_STATEMENT <=>
    ?eps0. &0 < eps0 /\
            !C eps g0 A0.
               &1 < C /\ &0 < eps /\ eps <= eps0 /\ p3_std_initial g0 A0
               ==> ?Kr. &0 < Kr /\
                     !G t x U.
                        p3_std_flow g0 (&1) G /\ &0 <= t /\ t < &1 /\
                        rfs_canonical_nbhd (euclidean,open_set_atlas (:real^3)) (G t)
                                           C eps x U
                        ==> !y l. y IN U /\ l <= 2
                                  ==> lrm_deriv_norm2 l
                                        (metric_local (open_set_atlas (:real^3))
                                           (chart_at (open_set_atlas (:real^3)) y)
                                           (\z. mfd_scalar (open_set_atlas (:real^3))
                                                  (G t) x %%
                                                G t z))
                                        (SND(chart_at (open_set_atlas (:real^3)) y) y) <= Kr`;;

(* ------------------------------------------------------------------------- *)
(* The route obligations.  Each P3_..._ROUTE statement constant says: these  *)
(* Part 3 results and Part 1-2 interfaces imply that Part 3 result (the      *)
(* dependency graph of the MT Ch 13-17 proofs, as used; u fixes the history  *)
(* type, w the type of geometric limits, (:real^3) the standard solution).   *)
(* Their proofs are in the Part 3 units.  P3_FULL_CHAIN derives              *)
(* RFS_EXTINCTION_STATEMENT from the obligations, the leaf statements, the   *)
(* interfaces, the Part 4 interface and the scaling and orientability        *)
(* inputs.  The PDE statements (pc_pde_iface) supply MT Thm 3.11, Prop 3.12, *)
(* Prop 4.11 (curvature part) and Prop 4.12.  Inputs of the routes: stage    *)
(* separation (RFS_CUTCAP_SC with APX_SC_SPHERE_SEP, the latter proved as    *)
(* SMT_SC_SPHERE_SEP in unit pc_smt_sep; P3_STRUCT_SPHERE_SEP below) enters  *)
(* Lemma 15.11 and Prop 17.1; Lemma 16.8 (in Prop 16.5) uses P2C_PROP_5_14   *)
(* and P2C_HISTORY_REGULAR; the repaired Claim 17.6 (points of the Thm 13.2  *)
(* region next to new caps are treated like exposed points, through the cap  *)
(* closeness of p3_cap_param, the standard solution (Thms 12.5, 12.32) and   *)
(* Prop 9.79; the others by the corrected Lemma 11.23) adds those inputs to  *)
(* Prop 17.1.  The route form P2_PROP_2_19_SEP with P2_SEP_LIMIT (p. 407)    *)
(* enters Prop 17.1, the open form P2_PROP_9_79_OPEN (p. 396) Lemma 17.2.    *)
(* The corrected neck form of Prop 9.79 needs a regular source view          *)
(* (histories: P2C_HISTORY_REGULAR; standard flows: P2C_FLOW_VIEW_REGULAR)   *)
(* and Riemannian target slices (histories: P3_HIST_VIEW_SLICES below); the  *)
(* corrected slice form needs the C^2 curvature bound on the source          *)
(* neighbourhoods (R13 for history slices, R14 for standard-flow slices);    *)
(* both enter Lemmas 17.2, 17.7 and Prop 17.1.  Lemmas 17.2 and 17.7 (MT     *)
(* pp. 401, 404) use Thm 12.5(5), B(p0,0,A) contains B(p0,theta,A/2),        *)
(* uniformly over all standard flows (there is no uniqueness); it follows    *)
(* from the uniform asymptotics of Prop 12.7, so P2_PROP_12_7 is a           *)
(* hypothesis of both routes.  Lemma 16.15 part (2) (MT p. 380-381) uses the *)
(* scalar curvature lower bound on the evolving cap regions from Prop 12.31  *)
(* and Thm 12.5, hypotheses of its route.  MT p. 407 applies Prop 2.19 to    *)
(* blow-up limits, which have only Rm >= 0, so the Prop 17.1 route and       *)
(* P3_FULL_CHAIN use the SEP form and not the plain Prop 2.19 (sec > 0, no   *)
(* separation).  Without the positive-curvature exemption (the canonical     *)
(* neighbourhoods carry KL's volume clause on C-components) the induction of *)
(* MT p. 393 needs no Thm 4.23.  Prop 16.1 follows the Kleiner-Lott route:   *)
(* KL Sublemma 79.23 in our setting (P3N_SMALL_SCALE_STATEMENT, unit         *)
(* pc_p3_s16sst, a leaf of the chain) and the large-scale case (MT Sec 16.6  *)
(* at the second scale rr: Props 16.4, 16.21, Cor 16.24, Lemma 14.11,        *)
(* Thm 8.1, Lemma 11.2; stage separation for the small scales); neither      *)
(* Prop 16.3 nor Lemma 7.2 is a hypothesis of the Prop 16.1 route, and       *)
(* Prop 16.3 is not one of P3_FULL_CHAIN.                                    *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;
type_invention_error := true;;

let P3_START_ROUTE_STATEMENT = new_definition
 `P3_START_ROUTE_STATEMENT (u:A->bool) <=>
    PDE_CURVATURE_TIME_STATEMENT (:A+num#num#real^3) (:3) /\
    P2_PROP_4_11_VOLUME_STATEMENT (:A+num#num#real^3) /\
    P2_THM_4_32_STATEMENT (:A+num#num#real^3)
    ==> P3_START_STATEMENT u`;;

let P3_FLOW_EXTENSION_ROUTE_STATEMENT = new_definition
 `P3_FLOW_EXTENSION_ROUTE_STATEMENT (u:A->bool) <=>
    PDE_MAXIMAL_FLOW_STATEMENT u (:3) /\ PDE_UNIQUENESS_STATEMENT u (:3) /\
    P2_THM_4_32_STATEMENT u
    ==> P3_FLOW_EXTENSION_STATEMENT u`;;

let P3_THM_13_2_ROUTE_STATEMENT = new_definition
 `P3_THM_13_2_ROUTE_STATEMENT <=>
    P2_LEMMA_12_37_STATEMENT ==> P3_THM_13_2_STATEMENT`;;

let P3_LEMMA_14_11_ROUTE_STATEMENT = new_definition
 `P3_LEMMA_14_11_ROUTE_STATEMENT (u:A->bool) <=>
    PDE_GLUE_STATEMENT u (:3) ==> P3_LEMMA_14_11_STATEMENT u`;;

let P3_LEMMA_15_11_ROUTE_STATEMENT = new_definition
 `P3_LEMMA_15_11_ROUTE_STATEMENT (u:A->bool) <=>
    P3_THM_13_2_STATEMENT /\
    PDE_MAXIMAL_FLOW_STATEMENT (:A+num#num#real^3) (:3) /\
    P2_THM_4_32_STATEMENT (:A+num#num#real^3) /\
    P2_THM_11_19_STATEMENT (:A+num#num#real^3) /\
    P2_LEMMA_11_30_STATEMENT (:A+num#num#real^3) /\
    P2_THM_11_31_STATEMENT (:A+num#num#real^3) /\ P2_LEMMA_12_3_STATEMENT /\
    RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
    APX_SC_SPHERE_SEP_STATEMENT (:A+num#num#real^3)
    ==> P3_LEMMA_15_11_STATEMENT u`;;

let P3_PROP_15_2_ROUTE_STATEMENT = new_definition
 `P3_PROP_15_2_ROUTE_STATEMENT (u:A->bool) <=>
    P2_THM_5_15_STATEMENT u (:real^3) ==> P3_PROP_15_2_STATEMENT u`;;

(* MT p. 373 uses                                                          *)
(* Prop 12.7 (the standard flow is close to a standard evolving cylinder on *)
(* B(p0,0,A) minus B(p0,0,A/2)) for the necks of Claim 16.10.              *)
let P3_PROP_16_5_ROUTE_STATEMENT = new_definition
 `P3_PROP_16_5_ROUTE_STATEMENT (u:A->bool) <=>
    P2_THM_3_28_STATEMENT u /\ P2_THM_3_29_STATEMENT u /\ P2_THM_5_15_STATEMENT u (:real^3) /\
    P2_THM_12_5_STATEMENT /\ P2_STD_EXTEND_STATEMENT /\ P2_LEMMA_11_2_STATEMENT u /\
    P3_LEMMA_14_11_STATEMENT u /\ P3_THM_13_2_STATEMENT /\
    P2C_PROP_5_14_STATEMENT u (:real^3) /\ P2C_HISTORY_REGULAR_STATEMENT u /\
    P2_PROP_12_7_STATEMENT
    ==> P3_PROP_16_5_STATEMENT u`;;

let P3_PROP_16_13_ROUTE_STATEMENT = new_definition
 `P3_PROP_16_13_ROUTE_STATEMENT (u:A->bool) <=>
    P3_PROP_16_5_STATEMENT u /\ P2_PROP_12_31_STATEMENT /\
    P2_PROP_12_7_STATEMENT /\ P2_THM_12_5_STATEMENT
    ==> P3_PROP_16_13_STATEMENT u`;;

let P3_LEMMA_16_15_ROUTE_STATEMENT = new_definition
 `P3_LEMMA_16_15_ROUTE_STATEMENT (u:A->bool) <=>
    P3_PROP_16_13_STATEMENT u /\ P3_PROP_16_5_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u /\
    P2_PROP_12_31_STATEMENT /\ P2_THM_12_5_STATEMENT
    ==> P3_LEMMA_16_15_STATEMENT u`;;

let P3_PROP_16_21_ROUTE_STATEMENT = new_definition
 `P3_PROP_16_21_ROUTE_STATEMENT (u:A->bool) <=>
    P3_LEMMA_16_15_STATEMENT u /\ P3_PROP_16_13_STATEMENT u /\
    P3_PROP_16_5_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u
    ==> P3_PROP_16_21_STATEMENT u`;;

let P3_COR_16_24_ROUTE_STATEMENT = new_definition
 `P3_COR_16_24_ROUTE_STATEMENT (u:A->bool) <=>
    P3_PROP_16_21_STATEMENT u /\ P2_LEMMA_7_2_STATEMENT u
    ==> P3_COR_16_24_STATEMENT u`;;

let P3_PROP_16_4_ROUTE_STATEMENT = new_definition
 `P3_PROP_16_4_ROUTE_STATEMENT (u:A->bool) <=>
    P3_COR_16_24_STATEMENT u /\ P3_PROP_16_21_STATEMENT u /\
    P2_LEMMA_7_2_STATEMENT u /\ P2_COR_7_12_STATEMENT u
    ==> P3_PROP_16_4_STATEMENT u`;;

let P3_PROP_16_1_ROUTE_STATEMENT = new_definition
 `P3_PROP_16_1_ROUTE_STATEMENT (u:A->bool) <=>
    P3N_SMALL_SCALE_STATEMENT u /\ P3_PROP_16_4_STATEMENT u /\
    P3_PROP_16_21_STATEMENT u /\ P3_COR_16_24_STATEMENT u /\
    P3_LEMMA_14_11_STATEMENT u /\ P2_THM_8_1_STATEMENT u /\
    P2_LEMMA_11_2_STATEMENT u /\ RFS_CUTCAP_SC_STATEMENT u u
    ==> P3_PROP_16_1_STATEMENT u`;;

let P3_LEMMA_17_2_ROUTE_STATEMENT = new_definition
 `P3_LEMMA_17_2_ROUTE_STATEMENT (u:A->bool) <=>
    P2_PROP_9_79_SLICE_STATEMENT u u /\ P2_PROP_9_79_SLICE_STATEMENT (:real^3) u /\
    P2_PROP_9_79_NECK_STATEMENT u u /\ P2_THM_12_32_STATEMENT /\
    P2_PROP_12_31_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_LEMMA_12_3_STATEMENT /\
    P3_PROP_16_5_STATEMENT u /\ P3_PROP_16_13_STATEMENT u /\ P3_THM_13_2_STATEMENT /\
    P2_PROP_9_79_OPEN_STATEMENT u u /\ P2C_HISTORY_REGULAR_STATEMENT u /\
    P3_HIST_C2_BOUND_STATEMENT u /\ P3_STD_C2_BOUND_STATEMENT /\ P2_PROP_12_7_STATEMENT
    ==> P3_LEMMA_17_2_STATEMENT u`;;

let P3_LEMMA_17_7_ROUTE_STATEMENT = new_definition
 `P3_LEMMA_17_7_ROUTE_STATEMENT (u:A->bool) <=>
    P3_PROP_16_5_STATEMENT u /\ P3_PROP_15_2_STATEMENT u /\
    P2_THM_12_32_STATEMENT /\ P2_PROP_9_79_SLICE_STATEMENT (:real^3) u /\
    P2_PROP_9_79_NECK_STATEMENT (:real^3) u /\ P2_PROP_12_31_STATEMENT /\
    P2_LEMMA_12_3_STATEMENT /\ P2_LEMMA_3_14_STATEMENT (:real^3) /\ P2_THM_12_5_STATEMENT /\
    P2C_HISTORY_REGULAR_STATEMENT u /\ P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
    P3_STD_C2_BOUND_STATEMENT /\ P2_PROP_12_7_STATEMENT
    ==> P3_LEMMA_17_7_STATEMENT u`;;

(* The route of Prop 17.1 includes P2_PROP_12_31 and history and flow-view   *)
(* regularity (used by the fresh-cap case and the canonv route).             *)

let P3_PROP_17_1_ROUTE_STATEMENT = new_definition
 `P3_PROP_17_1_ROUTE_STATEMENT (u:A->bool) (w:B->bool) <=>
    P3_LEMMA_17_2_STATEMENT u /\ P3_LEMMA_17_7_STATEMENT u /\
    P3_PROP_16_1_STATEMENT u /\
    P2_THM_11_8_STATEMENT u w /\ P2_COR_9_95_STATEMENT u w /\
    P2_THM_10_2_STATEMENT u /\ P2_LEMMA_11_2_STATEMENT u /\
    P2_LEMMA_11_23_STATEMENT u /\ P2_THM_5_11_STATEMENT u w /\
    P2_PROP_9_79_SLICE_STATEMENT u w /\
    RFS_CUTCAP_SC_STATEMENT u u /\ APX_SC_SPHERE_SEP_STATEMENT u /\
    P3_PROP_16_5_STATEMENT u /\ P3_THM_13_2_STATEMENT /\
    P2_THM_12_32_STATEMENT /\ P2_THM_12_5_STATEMENT /\
    P2_PROP_9_79_SLICE_STATEMENT (:real^3) u /\
    P2_PROP_2_19_SEP_STATEMENT w /\ P2_SEP_LIMIT_STATEMENT u w /\
    P3_HIST_C2_BOUND_STATEMENT u /\ P3_STD_C2_BOUND_STATEMENT /\
    P2_PROP_12_31_STATEMENT /\ P2C_HISTORY_REGULAR_STATEMENT u /\
    P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3)
    ==> P3_PROP_17_1_STATEMENT u`;;

let P3_LEMMA_17_12_ROUTE_STATEMENT = new_definition
 `P3_LEMMA_17_12_ROUTE_STATEMENT (u:A->bool) <=>
    P2_VOLUME_GROWTH_STATEMENT (:A+num#num#real^3) /\ P2_LEMMA_12_3_STATEMENT
    ==> P3_LEMMA_17_12_STATEMENT u`;;

(* ------------------------------------------------------------------------- *)
(* Stage separation on the route: with simply connected components at stage *)
(* 0 (p3_struct), cut-and-cap keeps components simply connected             *)
(* (RFS_CUTCAP_SC_STATEMENT, RFS_HISTORY_SC of unit pc_rfs_assembly), so    *)
(* every neck sphere of every stage separates (APX_SC_SPHERE_SEP_STATEMENT, *)
(* proved as SMT_SC_SPHERE_SEP in unit pc_smt_sep): the separation          *)
(* hypotheses of the corrected Thm 11.8, Lemma 11.30, Thm 11.31, Cor 9.95  *)
(* and Thm 10.2 (p2b_hs_sep) hold for the histories of the route.            *)
(* ------------------------------------------------------------------------- *)

let P3_STRUCT_SPHERE_SEP = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history).
        APX_SC_SPHERE_SEP_STATEMENT (:A) /\ RFS_CUTCAP_SC_STATEMENT (:A) (:A) /\
        p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs
        ==> p2b_hs_sep hs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_hs_sep] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sep") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `hs:(A)rfs_history` RFS_HISTORY_SC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "sc" o CONJUNCT1) THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REMOVE_THEN "sep" (MATCH_MP_TAC o REWRITE_RULE[APX_SC_SPHERE_SEP_STATEMENT]) THEN
  SUBGOAL_THEN `hausdorff_space (hs_top (hs:(A)rfs_history) k) /\
                smooth_manifold_atlas (hs_top hs k) (hs_atlas hs k)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [rfs_history_ok]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `rfs_components_sc (hs_top (hs:(A)rfs_history) k)` MP_TAC THENL
   [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[rfs_components_sc]]);;

(* ------------------------------------------------------------------------- *)
(* The slices of a history view are smooth Riemannian manifolds at          *)
(* every time (empty slices with the empty atlas outside [0, horizon)): the *)
(* target-slice hypothesis of the corrected P2_PROP_9_79_NECK for history   *)
(* targets (Lemmas 17.2, 17.7).                                              *)
(* ------------------------------------------------------------------------- *)

let P3_HIST_VIEW_SLICES = prove
 (`!(hs:(A)rfs_history) t.
        rfs_history_ok hs
        ==> smooth_manifold_atlas (rfs_vtop (rfs_view hs) t) (rfs_vatlas (rfs_view hs) t) /\
            riemannian_metric (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric] THEN
  REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[smooth_manifold_atlas; riemannian_metric; NOT_IN_EMPTY;
                TOPSPACE_DISCRETE_TOPOLOGY]] THEN
  MP_TAC(SPECL [`hs:(A)rfs_history`; `t:real`] RFS_SLAB) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `rfs_live (hs:(A)rfs_history) t` THEN
    ASM_REWRITE_TAC[rfs_live; rfs_horizon];
    ALL_TAC] THEN
  ABBREV_TAC `k = rfs_slab (hs:(A)rfs_history) t` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = hs_time (hs:(A)rfs_history) k` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The full chain: obligations + leaves + interfaces + Part 4 interface +    *)
(* scaling + orientability give RFS_EXTINCTION_STATEMENT.  The leaf of Part  *)
(* 3 besides the obligations is P3N_SMALL_SCALE_STATEMENT; the history type  *)
(* is A + num#num#real^3, limits live on w.                                  *)
(* ------------------------------------------------------------------------- *)

let P3_FULL_CHAIN = prove
 (`!(u:A->bool) (w:B->bool).
     P3_START_ROUTE_STATEMENT u /\
     P3_FLOW_EXTENSION_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_THM_13_2_ROUTE_STATEMENT /\
     P3_LEMMA_14_11_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_15_11_ROUTE_STATEMENT u /\
     P3_PROP_15_2_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_5_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_13_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_16_15_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_21_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_COR_16_24_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_4_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_16_1_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_17_2_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_LEMMA_17_7_ROUTE_STATEMENT (:A+num#num#real^3) /\
     P3_PROP_17_1_ROUTE_STATEMENT (:A+num#num#real^3) w /\
     P3_LEMMA_17_12_ROUTE_STATEMENT u /\
     P3N_SMALL_SCALE_STATEMENT (:A+num#num#real^3) /\
     PDE_CURVATURE_TIME_STATEMENT (:A+num#num#real^3) (:3) /\
     PDE_MAXIMAL_FLOW_STATEMENT (:A+num#num#real^3) (:3) /\
     PDE_UNIQUENESS_STATEMENT (:A+num#num#real^3) (:3) /\
     PDE_GLUE_STATEMENT (:A+num#num#real^3) (:3) /\
     P2_THM_3_28_STATEMENT (:A+num#num#real^3) /\
     P2_THM_3_29_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_3_14_STATEMENT (:real^3) /\
     P2_PROP_4_11_VOLUME_STATEMENT (:A+num#num#real^3) /\
     P2_THM_4_32_STATEMENT (:A+num#num#real^3) /\
     P2_VOLUME_GROWTH_STATEMENT (:A+num#num#real^3) /\
     P2_THM_5_11_STATEMENT (:A+num#num#real^3) w /\
     P2_THM_5_15_STATEMENT (:A+num#num#real^3) (:real^3) /\
     P2_THM_8_1_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_7_2_STATEMENT (:A+num#num#real^3) /\
     P2_COR_7_12_STATEMENT (:A+num#num#real^3) /\
     P2_PROP_9_79_SLICE_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     P2_PROP_9_79_SLICE_STATEMENT (:real^3) (:A+num#num#real^3) /\
     P2_PROP_9_79_SLICE_STATEMENT (:A+num#num#real^3) w /\
     P2_PROP_9_79_NECK_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     P2_PROP_9_79_NECK_STATEMENT (:real^3) (:A+num#num#real^3) /\
     P2_COR_9_95_STATEMENT (:A+num#num#real^3) w /\
     P2_THM_10_2_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_11_2_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_8_STATEMENT (:A+num#num#real^3) w /\
     P2_LEMMA_11_23_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_19_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_11_30_STATEMENT (:A+num#num#real^3) /\
     P2_THM_11_31_STATEMENT (:A+num#num#real^3) /\
     P2_LEMMA_12_3_STATEMENT /\ P2_THM_12_5_STATEMENT /\ P2_STD_EXTEND_STATEMENT /\
     P2_PROP_12_7_STATEMENT /\
     P2_PROP_12_31_STATEMENT /\ P2_THM_12_32_STATEMENT /\ P2_LEMMA_12_37_STATEMENT /\
     P2C_PROP_5_14_STATEMENT (:A+num#num#real^3) (:real^3) /\
     P2C_HISTORY_REGULAR_STATEMENT (:A+num#num#real^3) /\
     RFS_CUTCAP_SC_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     APX_SC_SPHERE_SEP_STATEMENT (:A+num#num#real^3) /\
     P2_PROP_2_19_SEP_STATEMENT w /\
     P2_SEP_LIMIT_STATEMENT (:A+num#num#real^3) w /\
     P2_PROP_9_79_OPEN_STATEMENT (:A+num#num#real^3) (:A+num#num#real^3) /\
     P2C_FLOW_VIEW_REGULAR_STATEMENT (:real^3) /\
     P3_HIST_C2_BOUND_STATEMENT (:A+num#num#real^3) /\ P3_STD_C2_BOUND_STATEMENT /\
     P4_EXTINCTION_STATEMENT u /\ P2_NORMALIZE_STATEMENT u /\
     SMT_ORIENTABLE_STATEMENT u (:3)
     ==> RFS_EXTINCTION_STATEMENT u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[P3_START_ROUTE_STATEMENT; P3_FLOW_EXTENSION_ROUTE_STATEMENT;
              P3_THM_13_2_ROUTE_STATEMENT; P3_LEMMA_14_11_ROUTE_STATEMENT;
              P3_LEMMA_15_11_ROUTE_STATEMENT; P3_PROP_15_2_ROUTE_STATEMENT;
              P3_PROP_16_5_ROUTE_STATEMENT; P3_PROP_16_13_ROUTE_STATEMENT;
              P3_LEMMA_16_15_ROUTE_STATEMENT; P3_PROP_16_21_ROUTE_STATEMENT;
              P3_COR_16_24_ROUTE_STATEMENT; P3_PROP_16_4_ROUTE_STATEMENT;
              P3_PROP_16_1_ROUTE_STATEMENT; P3_LEMMA_17_2_ROUTE_STATEMENT;
              P3_LEMMA_17_7_ROUTE_STATEMENT; P3_PROP_17_1_ROUTE_STATEMENT;
              P3_LEMMA_17_12_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `P3_THM_13_2_STATEMENT` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_14_11_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_15_2_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_5_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_13_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_16_15_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_21_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_COR_16_24_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_4_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_16_1_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_17_2_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_17_7_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_PROP_17_1_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_15_11_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_FLOW_EXTENSION_STATEMENT (:A+num#num#real^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_LEMMA_17_12_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P3_START_STATEMENT (u:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC P3_RFS_EXTINCTION THEN ASM_REWRITE_TAC[]);;

