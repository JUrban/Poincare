(* ========================================================================= *)
(* Unit pc_p3_s16sst: the statement of the small-scale part of MT Prop 16.1, *)
(* i.e. Kleiner-Lott Sublemma 79.23 in the setting of a Ricci flow with      *)
(* surgery (MT's proof treats a point of large curvature only at the scale   *)
(* R^(-1/2), while Def 14.15 quantifies over every scale r <= r0).  Proved   *)
(* in unit pc_p3_s16small (|- !u. P3N_SMALL_SCALE_STATEMENT u); used by the  *)
(* assembly of Prop 16.1 in pc_p3_route, which supplies the large-scale      *)
(* bound at rr, the canonical neighbourhood threshold Rthr = r'^-2 and the   *)
(* hot caps.                                                                 *)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* For C > 1 there are Lam >= 1 and kS > 0 such that: in a history with     *)
(* pinching and simply connected components, where every point with         *)
(* R >= Rthr (Rthr >= 8 e^4 C, Lam Rthr <= rr^-2) has a canonical           *)
(* neighbourhood (p3_canonv_at) and every surgery cap point has R >=        *)
(* Lam Rthr at its surgery time, a ball B(x0,t0,r0), r0 <= rr, rr^2 <= t0,  *)
(* with P(x0,t0,r0) and abs Rm <= r0^-2 there has volume >=                 *)
(* min (kL/2) kS r0^3, provided the same holds at the scale rr with kL.      *)

let P3N_SMALL_SCALE_STATEMENT = new_definition
 `P3N_SMALL_SCALE_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C. &1 < C
        ==> ?Lam kS. &1 <= Lam /\ &0 < kS /\
              !(hs:(A)rfs_history) eps Rthr rr kL x0 t0 r0.
                rfs_history_ok hs /\ rfs_pinched (rfs_view hs) /\
                (!t. &0 <= t /\ t < rfs_horizon hs
                     ==> rfs_components_sc (rfs_vtop (rfs_view hs) t)) /\
                &0 < eps /\ eps <= eps0 /\ &8 * exp(&4) * C <= Rthr /\
                Lam * Rthr <= inv(rr pow 2) /\
                (!t y. &0 <= t /\ y IN topspace(rfs_vtop (rfs_view hs) t) /\
                       Rthr <= rfs_vscalar (rfs_view hs) t y
                       ==> p3_canonv_at (rfs_view hs) C eps y t) /\
                (!k i c. 1 <= k /\ k <= hs_count hs /\
                         t0 - rr pow 2 <= hs_time hs k /\ hs_time hs k <= t0 /\
                         i IN ev_index(hs_event hs k) /\
                         c IN IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1))
                         ==> Lam * Rthr <= rfs_vscalar (rfs_view hs) (hs_time hs k) c) /\
                &0 < kL /\ rr pow 2 <= t0 /\ t0 < rfs_horizon hs /\
                x0 IN topspace(rfs_vtop (rfs_view hs) t0) /\ &0 < r0 /\ r0 <= rr /\
                rfs_parabolic_exists (rfs_view hs) t0 x0 r0 (r0 pow 2) /\
                (!t y. t0 - r0 pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 r0
                       ==> mfd_rm_norm (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t) y
                           <= inv(r0 pow 2)) /\
                (rfs_parabolic_exists (rfs_view hs) t0 x0 rr (rr pow 2) /\
                 (!t y. t0 - rr pow 2 < t /\ t <= t0 /\ y IN rfs_vball (rfs_view hs) t0 x0 rr
                        ==> mfd_rm_norm (rfs_vatlas (rfs_view hs) t) (rfs_vmetric (rfs_view hs) t) y
                            <= inv(rr pow 2))
                 ==> ?v. mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                        (rfs_vmetric (rfs_view hs) t0)
                                        (rfs_vball (rfs_view hs) t0 x0 rr) v /\
                         kL * rr pow 3 <= v)
                ==> ?v. mfd_has_volume (rfs_vtop (rfs_view hs) t0,rfs_vatlas (rfs_view hs) t0)
                                       (rfs_vmetric (rfs_view hs) t0)
                                       (rfs_vball (rfs_view hs) t0 x0 r0) v /\
                        min (kL / &2) kS * r0 pow 3 <= v`;;

