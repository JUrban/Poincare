(* ========================================================================= *)
(* Unit pc_p2b_chainstmts (Part 2B): STATEMENTS ONLY for the Ch 9 core       *)
(* between Prop 9.20 and the classification of kappa-solutions: the          *)
(* asymptotic-soliton statement P2B_ASYM_SOLITON_STATEMENT and the           *)
(* statements of the soliton part (MT Thm 9.11 without the classification;   *)
(* pc_p2b_t911, pc_p2b_sol), the splitting part (splitting at infinity, the  *)
(* split classification replacing KSOL2_ROUND, flat forward; pc_p2b_x0lim,   *)
(* pc_p2b_x1, pc_p2b_x2, pc_p2b_x2s, pc_p2b_sround, pc_p2b_flatfwd) and the  *)
(* shrinker part (Cor 9.53, Prop 9.46, Thm 9.42 with Cor 9.54 in flow form,  *)
(* the classification; pc_p2b_p946, pc_p2b_shrinkcl), with their route       *)
(* obligations, the four chain theorems and P2B_ASYM_FROM_PARTS.  Prop 2.19  *)
(* is used in the separating form P2_PROP_2_19_SEP_STATEMENT of pc_p3_iface, *)
(* and the route of X0 has no splitting input (the theorem CMP_R3_SPLIT of   *)
(* pc_cmp_split is used inside the proof).                                   *)
(*                                                                           *)
(* X0 (P2B_SPLIT_AT_INFINITY) and X2 (P2B_CYL_AT_INFINITY) conclude with a   *)
(* subsequence sub and compare R(pp (sub k)) with R(q k): an index-wise      *)
(* comparison would be unprovable, since the limits exist only along         *)
(* subsequences.                                                             *)
(*                                                                           *)
(* Further statements: P2B_ASYM_SOLITON_AT_STATEMENT (at a given base point, *)
(* with the l <= 3/2 bound) and P2B_COR_9_44_STATEMENT, THM_9_11 at a base   *)
(* point and its route; X2 and X2s also conclude that the limit is smooth up *)
(* to 0 (rfs_flow_upto), X2s with limits at the given points; the route of   *)
(* SPLIT_ROUND takes ANCIENT_COMPACT and the entropy statement               *)
(* P2B_REQ_S2_ENTROPY_STATEMENT; the routes of COR_9_44, Prop 9.58 and Thm   *)
(* 9.59; P2B_ASYM_AT_FROM_PARTS and the implications to the plain forms.     *)
(*                                                                           *)
(* P2B_COR_9_44_STATEMENT has the hypothesis that the limit slice is a       *)
(* Riemannian metric (the curvature stability needs a metric field).  Then   *)
(* P2B_LEMMA_9_65_ROUTE_STATEMENT (Tao's route), the final-slice statements  *)
(* (the class p2b_ancflow0c, X0_FINAL, X2_FINAL,                             *)
(* P2B_COR_9_53_FINAL_STATEMENT, their routes and P2B_FINAL_CHAIN),          *)
(* P2B_THM_9_64_ROUTE_STATEMENT and the routes of Cor 9.71 and A5L.          *)
(*                                                                           *)
(* First: needs lines and the statements P2B_ASYM_SOLITON_STATEMENT,         *)
(* P2B_ASYM_SOLITON_AT_STATEMENT and P2B_COR_9_44_STATEMENT.                 *)
(* ========================================================================= *)

needs "src/pc_p2b_defs.ml";;
needs "src/pc_p2b_shrinkreq.ml";;
needs "src/pc_p2b_w920g.ml";;
needs "src/pc_p2b_pinch3req.ml";;
needs "src/pc_p2b_s2entreq.ml";;
needs "src/pc_p2b_flatreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* C3. MT Thm 9.11 with Cors 9.53, 9.54 (and Thm 9.42, Prop 9.46): the      *)
(* asymptotic gradient shrinking soliton.  Rescalings g(tau_k s')/tau_k     *)
(* based at (q_k, -tau_k) converge on the limit times s < 1 (MT's time      *)
(* t = s - 1 < 0); at s = 0 (MT t = -1) Ric + Hess f = g/2; shifted by 1/2 *)
(* it is a kappa-solution of the same class; it is compact round or the     *)
(* cylinder model.                                                           *)
(* ------------------------------------------------------------------------- *)

let P2B_ASYM_SOLITON_STATEMENT = new_definition
 `P2B_ASYM_SOLITON_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3).
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas
       ==> ?tau q (top':B topology) atlas' g' xl f.
              (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
              (!k. q k IN topspace top) /\
              p3_flow_limit_on (\k. p2b_kview (top,atlas) g) q (\k. --(tau k))
                               (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
              p2b_shrinker (top',atlas') (g'(&0)) f /\
              p2b_kappa_solution kappa (top',atlas') (\t. g'(t + &1 / &2)) /\
              p2b_ksep top' atlas' /\
              ((compact_space top' /\ p2b_round (top',atlas') (g'(&0))) \/
               p2b_cyl_model (top',atlas') (\t. g'(t + &1 / &2)))`;;

(* C3a (for MT Prop 9.58): the asymptotic soliton at a GIVEN base point p,   *)
(* with the points q k chosen so that the reduced length from (p,0) at       *)
(* backward time tau k is at most 3/2 (MT Thm 9.11 picks them by Thm 7.10    *)
(* and Claim 7.11).  It implies P2B_ASYM_SOLITON_STATEMENT                   *)
(* (P2B_ASYM_SOLITON_AT_IMP, below).                                         *)

let P2B_ASYM_SOLITON_AT_STATEMENT = new_definition
 `P2B_ASYM_SOLITON_AT_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p.
       p2b_kappa_solution kappa (top,atlas) g /\ p2b_ksep top atlas /\ p IN topspace top
       ==> ?tau q (top':B topology) atlas' g' xl f.
              (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
              (!k. q k IN topspace top) /\
              (!k. p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
              p3_flow_limit_on (\k. p2b_kview (top,atlas) g) q (\k. --(tau k))
                               (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
              p2b_shrinker (top',atlas') (g'(&0)) f /\
              p2b_kappa_solution kappa (top',atlas') (\t. g'(t + &1 / &2)) /\
              p2b_ksep top' atlas' /\
              ((compact_space top' /\ p2b_round (top',atlas') (g'(&0))) \/
               p2b_cyl_model (top',atlas') (\t. g'(t + &1 / &2)))`;;

(* C3b (for MT Prop 9.58): MT Cor 9.44 in shift form.  If the rescalings of  *)
(* the shifted flow g(t + t0) based at (q k, -tau k), tau k -> infinity,     *)
(* converge to a limit that is compact and round at limit time 0, then g(0)  *)
(* is round (M is compact, the slices g(t0 - tau k) are almost round;        *)
(* Hamilton's pinching R-PINCH3, P2B_REQ_PINCH_ROUND3_STATEMENT; continuity  *)
(* of the curvature at 0).  The limit slice g'(0) is assumed to be a         *)
(* Riemannian metric (P2B_PROP_9_58_ROUTE gets it from the kappa-solution    *)
(* clause of ASYM_SOLITON_AT).                                               *)

let P2B_COR_9_44_STATEMENT = new_definition
 `P2B_COR_9_44_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) t0 tau q (top':B topology) atlas' g' xl.
       p2b_kappa_solution kappa (top,atlas) g /\ t0 <= &0 /\
       (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
       (!k. q k IN topspace top) /\
       p3_flow_limit_on (\k. p2b_kview (top,atlas) (\t. g(t + t0))) q (\k. --(tau k))
                        (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
       compact_space top' /\ riemannian_metric atlas' (g'(&0)) /\
       p2b_round (top',atlas') (g'(&0))
       ==> p2b_round (top,atlas) (g(&0))`;;

(* ========================================================================= *)
(* The soliton part.                                                         *)
(* ========================================================================= *)

(* The class of ancient flows without the separation hypothesis              *)
(* (p2b_ancflow, below, is defined on top of it).                            *)

let p2b_ancflow0 = new_definition
 `p2b_ancflow0 (kappa:real) (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
               (g:real->B->real^3^3) (b:real) <=>
    &0 < kappa /\ hausdorff_space top /\ connected_space top /\ ~(topspace top = {}) /\
    (!a. a < b ==> ricci_flow_on (top,atlas) a b g) /\
    (!s. s < b ==> mfd_complete (top,atlas) (g s)) /\
    (!s x u v. s < b /\ x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional atlas (g s) x u v) /\
    (!s. s < b ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g s) x) /\
    (!s x dR. s < b /\ x IN topspace top /\
              ((\t. mfd_scalar atlas (g t) x) has_real_derivative dR) (atreal s)
              ==> &0 <= dR) /\
    (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {s | s < b} g) kappa r0)`;;

(* ------------------------------------------------------------------------- *)
(* S1. MT Thm 9.11 without the classification.  For a kappa-solution there   *)
(* are tau k -> infinity and points q k such that the rescaled based flows   *)
(* converge on limit times s < 1 (MT time s - 1) to a flow in the class on s *)
(* < 1 that satisfies the shrinker equation at EVERY time (Prop 9.32 at      *)
(* every tau, which Cor 9.54 needs), with f(s) = linf(1 - s).  No separation *)
(* hypothesis.  P2B_ASYM_SOLITON = this + P2B_KSEP_LIMIT + P2B_SOLITON_CLASS *)
(* (P2B_ASYM_FROM_PARTS).                                                    *)
(* ------------------------------------------------------------------------- *)

let P2B_THM_9_11_STATEMENT = new_definition
 `P2B_THM_9_11_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3).
       p2b_kappa_solution kappa (top,atlas) g
       ==> ?tau q (top':B topology) atlas' g' xl f.
              (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
              (!k. q k IN topspace top) /\
              p3_flow_limit_on (\k. p2b_kview (top,atlas) g) q (\k. --(tau k))
                               (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
              p2b_ancflow0 kappa (top',atlas') g' (&1) /\
              (!s. s < &1 ==> p2b_shrinker (top',atlas') (\x. inv(&1 - s) %% g' s x) (f s))`;;

(* S1a: THM_9_11 at a given base point p, exporting the bound l(q k, tau k)  *)
(* <= 3/2 of the reduced length from (p,0) by which the points q k are       *)
(* chosen (MT Thm 7.10, Claim 7.11).  It implies P2B_THM_9_11_STATEMENT      *)
(* (P2B_THM_9_11_AT_IMP below).                                              *)

let P2B_THM_9_11_AT_STATEMENT = new_definition
 `P2B_THM_9_11_AT_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p.
       p2b_kappa_solution kappa (top,atlas) g /\ p IN topspace top
       ==> ?tau q (top':B topology) atlas' g' xl f.
              (!k. &0 < tau k) /\ (!M. ?N. !k. N <= k ==> M < tau k) /\
              (!k. q k IN topspace top) /\
              (!k. p2b_klx (top,atlas) g p (tau k) (q k) <= &3 / &2) /\
              p3_flow_limit_on (\k. p2b_kview (top,atlas) g) q (\k. --(tau k))
                               (\k. inv(tau k)) {s | s < &1} (top',atlas') g' xl /\
              p2b_ancflow0 kappa (top',atlas') g' (&1) /\
              (!s. s < &1 ==> p2b_shrinker (top',atlas') (\x. inv(&1 - s) %% g' s x) (f s))`;;

(* ------------------------------------------------------------------------- *)
(* S2. MT Sections 2.7-2.8 (Prop 9.32 with Lemma 9.33 and Claims 9.34, 9.35; *)
(* Claim 9.36), from the output of Prop 9.20: on a connected Ricci flow on s *)
(* < 1 with complete slices, a function linf smooth in every chart with      *)
(* (9.4) and (9.5) at every point gives the shrinker equation Ric + Hess     *)
(* linf(tau) = g / (2 tau) at every time (v = tau (2 Lap f - |grad f|^2 + R) *)
(* + f - n vanishes by (9.5), and (d/dtau - Lap + R) v = -2 tau |Ric + Hess  *)
(* f - g/(2 tau)|^2 u); with a reduced volume V < (4 pi)^(3/2) no slice is   *)
(* flat (a flat slice is R^3 by exp at the minimum of f, f = |x + 2 tau a|^2 *)
(* / (4 tau) by (9.5), and the Gaussian integral is (4 pi)^(3/2)).           *)
(* ------------------------------------------------------------------------- *)

let P2B_SOLITON_FROM_LINF_STATEMENT = new_definition
 `P2B_SOLITON_FROM_LINF_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) (linf:real->B->real) V.
       hausdorff_space top /\ connected_space top /\
       (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) g) /\
       (!s. s < &1 ==> mfd_complete (top,atlas) (g s)) /\
       (!c tmax. c IN atlas
                 ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
       (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
              ==> wan_tder (p2bw_cfun c linf) z +
                  lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                         (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                  p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                  llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                  &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                            (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                  lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                         (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                  p2bw_cscal atlas c (&1) g z +
                  (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
       p2bg_rvol (top,atlas) g linf V /\ V < sqrt(&4 * pi) pow 3
       ==> (!s. s < &1
                ==> p2b_shrinker (top,atlas) (\x. inv(&1 - s) %% g s x) (linf (&1 - s))) /\
           (!s. s < &1 ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g s) x)`;;

(* The leaf, with the hypothesis ~(topspace top = {}): for the empty space   *)
(* the second conclusion fails.  The bridge                                  *)
(* P2B_SOLITON_FROM_LINF_ORIG_IMP_FIX is in pc_p2b_gaussreq.                 *)

let P2B_SOLITON_FROM_LINF_FIX_STATEMENT = new_definition
 `P2B_SOLITON_FROM_LINF_FIX_STATEMENT (w:B->bool) <=>
    !top atlas (g:real->B->real^3^3) (linf:real->B->real) V.
       ~(topspace top = {}) /\ hausdorff_space top /\ connected_space top /\
       (!a. a < &1 ==> ricci_flow_on (top,atlas) a (&1) g) /\
       (!s. s < &1 ==> mfd_complete (top,atlas) (g s)) /\
       (!c tmax. c IN atlas
                 ==> smooth_map_on (p2bw_cdom c tmax) (\z. lift(p2bw_cfun c linf z))) /\
       (!c z. c IN atlas /\ fstcart z IN IMAGE (SND c) (FST c) /\ &0 < drop(sndcart z)
              ==> wan_tder (p2bw_cfun c linf) z +
                  lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                         (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                  p2bw_cscal atlas c (&1) g z + &3 / (&2 * drop(sndcart z)) -
                  llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                       (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) = &0 /\
                  &2 * llap (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                            (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) -
                  lgrad2 (p2bw_slice (p2bw_cmet atlas c (&1) g) z)
                         (p2bw_fslice (p2bw_cfun c linf) z) (fstcart z) +
                  p2bw_cscal atlas c (&1) g z +
                  (p2bw_cfun c linf z - &3) / drop(sndcart z) = &0) /\
       p2bg_rvol (top,atlas) g linf V /\ V < sqrt(&4 * pi) pow 3
       ==> (!s. s < &1
                ==> p2b_shrinker (top,atlas) (\x. inv(&1 - s) %% g s x) (linf (&1 - s))) /\
           (!s. s < &1 ==> ?x. x IN topspace top /\ &0 < mfd_rm_norm atlas (g s) x)`;;

(* ------------------------------------------------------------------------- *)
(* Route obligations of the soliton part.                                    *)
(* ------------------------------------------------------------------------- *)

(* Thm 9.11 (MT pp. 185-188, 198-203): q k from FL4 with l(q k, tau k) <=    *)
(* 3/2; Cor 9.10 (Claim 9.15, Cor 9.16) bounds l and R <= 3 l / t on the     *)
(* balls of g(-tau0 tau k) about q k, distances do not decrease backward     *)
(* (sec >= 0) and R does not increase backward (KSOL_DRDT), so abs Rm <= R   *)
(* is bounded on the balls of the base slice over all times <= -tau0;        *)
(* compactness backward from s = 0 (ANCIENT_COMPACT, complete slice at 0)    *)
(* and forward to s < 1 with the same W, phi (P2C_PROP_5_14, kviews regular  *)
(* by a Part 2B lemma from rfs_flow_upto); the limit is connected (component *)
(* of xl), kappa-noncollapsed, sec >= 0, dR/ds >= 0, complete for s <= 0     *)
(* (distances do not decrease backward) and for 0 < s < 1 (R <= C(s,D) on    *)
(* g(s)-balls of radius D by the transferred Cor 9.16, then R <= C on them   *)
(* for all earlier times by dR/ds >= 0, so g(s)-balls lie in g(0)-balls);    *)
(* then PROP_9_20 (its setup checked) gives linf, (9.4), (9.5), V; then      *)
(* SOLITON_FROM_LINF.                                                        *)

let P2B_THM_9_11_ROUTE_STATEMENT = new_definition
 `P2B_THM_9_11_ROUTE_STATEMENT (w:B->bool) <=>
    P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
    P2B_PROP_9_20_STATEMENT w w /\ P2B_SOLITON_FROM_LINF_FIX_STATEMENT w /\
    P2B_KSOL_DRDT_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
    P2C_PROP_5_14_STATEMENT w w
    ==> P2B_THM_9_11_STATEMENT w`;;

(* THM_9_11_AT: the same inputs (the proof in pc_p2b_t911 picks the points q *)
(* k for an arbitrary base point by P2A_FLOW_THM_7_10).                      *)

let P2B_THM_9_11_AT_ROUTE_STATEMENT = new_definition
 `P2B_THM_9_11_AT_ROUTE_STATEMENT (w:B->bool) <=>
    P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
    P2B_PROP_9_20_STATEMENT w w /\ P2B_SOLITON_FROM_LINF_FIX_STATEMENT w /\
    P2B_KSOL_DRDT_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
    P2C_PROP_5_14_STATEMENT w w
    ==> P2B_THM_9_11_AT_STATEMENT w`;;

(* SOLITON_FROM_LINF_FIX: proved in route form in pc_p2b_sol                 *)
(* (P2B_SOLITON_FROM_LINF_FIX_ROUTE: Lemma 9.33 in charts with the heat      *)
(* calculus of the pc_rfa units; the flat case from the route input          *)
(* P2B_REQ_FLAT_GAUSS of pc_p2b_gaussreq, a statement on the Gaussian        *)
(* soliton).  No route statement here.                                       *)

(* The composed chain of the soliton part.                                   *)

let P2B_SOL_CHAIN = prove
 (`!w:B->bool.
     P2B_THM_9_11_ROUTE_STATEMENT w /\
     P2A_FLOW_THM_7_10_STATEMENT w (:3) /\ P2B_COR_9_10_STATEMENT w /\
     P2B_PROP_9_20_STATEMENT w w /\ P2B_SOLITON_FROM_LINF_FIX_STATEMENT w /\
     P2B_KSOL_DRDT_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
     P2C_PROP_5_14_STATEMENT w w
     ==> P2B_THM_9_11_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_THM_9_11_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The based form implies the plain one (kappa-solutions are nonempty). *)

let P2B_THM_9_11_AT_IMP = prove
 (`!w:B->bool. P2B_THM_9_11_AT_STATEMENT w ==> P2B_THM_9_11_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_THM_9_11_AT_STATEMENT; P2B_THM_9_11_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?p:B. p IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                                `p:B`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                       `xl:B`; `f:real->B->real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `f:real->B->real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The splitting part.                                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* V1. The class of ancient flows without and with the separation            *)
(* hypothesis: on s < b, connected and nonempty, complete slices of          *)
(* nonnegative sectional curvature, non-flat at every time, dR/ds >= 0,      *)
(* kappa-noncollapsed on all scales: p2b_ancflow0 (defined above in the      *)
(* soliton part); p2b_ancflow adds p2b_ksep (needed only to exclude RP^2 x R *)
(* and to have separating neck spheres).                                     *)
(* ------------------------------------------------------------------------- *)

let p2b_ancflow = new_definition
 `p2b_ancflow (kappa:real) (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
              (g:real->B->real^3^3) (b:real) <=>
    p2b_ancflow0 kappa (top,atlas) g b /\ p2b_ksep top atlas`;;

(* A global unit vector field parallel for every metric g(s), s in J. *)

let p2b_gsplit = new_definition
 `p2b_gsplit (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3)
             (J:real->bool) (X:B->real^3) <=>
    !s. s IN J
        ==> p2b_parallel_on atlas (g s) (topspace top) X /\
            !y. y IN topspace top ==> X y dot (g s y ** X y) = &1`;;

(* ------------------------------------------------------------------------- *)
(* S1. X0, MT Prop 9.39 without the identification of the factor (Thm 5.35   *)
(* splits the time-0 slice globally, and the parallel field stays parallel   *)
(* backward in time): along p k with R(p k) d^2(p,p k) -> infinity at time   *)
(* s0 there are a subsequence sub and q k with R(q k) >= R(p (sub k)) and    *)
(* R(q k) d^2 -> infinity (the limit exists only along a subsequence) whose  *)
(* rescaled based flows (scale R(q k), backward times s <= 0) converge; the  *)
(* limit is connected, smooth up to 0, complete, sec >= 0, R = 1 at the base *)
(* point at time 0, of bounded curvature, kappa-noncollapsed, dR/ds >= 0,    *)
(* and has a global parallel unit field for all s <= 0.  No 2-d input        *)
(* (KSOL2_ROUND, SPLIT_ROUND), so the split trick below does not loop.       *)
(* ------------------------------------------------------------------------- *)

let P2B_SPLIT_AT_INFINITY_STATEMENT = new_definition
 `P2B_SPLIT_AT_INFINITY_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) b s0 p pp.
       p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\ p IN topspace top /\
       (!k. pp k IN topspace top) /\
       (!M. ?N. !k. N <= k
                    ==> M < mfd_scalar atlas (g s0) (pp k) *
                            mfd_dist (top,atlas) (g s0) p (pp k) pow 2)
       ==> ?sub q (top':B topology) atlas' g' xl W phi X.
              p3_subseq sub /\
              (!k. q k IN topspace top /\
                   mfd_scalar atlas (g s0) (pp (sub k)) <= mfd_scalar atlas (g s0) (q k)) /\
              (!M. ?N. !k. N <= k
                           ==> M < mfd_scalar atlas (g s0) (q k) *
                                   mfd_dist (top,atlas) (g s0) p (q k) pow 2) /\
              p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s < b} g) q (\k. s0)
                                  (\k. mfd_scalar atlas (g s0) (q k)) {s | s <= &0}
                                  (top',atlas') g' xl W phi /\
              connected_space top' /\
              (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
              (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
              (!s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                         ==> &0 <= mfd_sectional atlas' (g' s) y u v) /\
              mfd_scalar atlas' (g'(&0)) xl = &1 /\
              (?K. !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= K) /\
              (!r0. rfs_kappa_noncollapsed (rfs_flow_view (top',atlas') {s | s <= &0} g')
                                           kappa r0) /\
              (!s y dR. s <= &0 /\ y IN topspace top' /\
                        ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                        ==> &0 <= dR) /\
              p2b_gsplit (top',atlas') g' {s | s <= &0} X`;;

(* S2. The split classification (replaces KSOL2_ROUND in every use): a     *)
(* class flow with a global parallel unit field and orientable relatively  *)
(* compact open sets is, up to every time s0 < b, the round cylinder model. *)

let P2B_SPLIT_ROUND_STATEMENT = new_definition
 `P2B_SPLIT_ROUND_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) b X.
       p2b_ancflow0 kappa (top,atlas) g b /\ p2b_lorient top atlas /\
       p2b_gsplit (top,atlas) g {s | s < b} X
       ==> !s0. s0 < b ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`;;

(* ------------------------------------------------------------------------- *)
(* S3. The interface of the shrinker part.                                   *)
(* ------------------------------------------------------------------------- *)

(* X1 (Prop 9.83 / Claim 9.45 / Cor 9.53 first case for the class): a zero  *)
(* plane at (x0,s0) makes the flow up to s0 the round cylinder model or its *)
(* orientable Z/2 quotient (SMP splitting backward in time; a global field  *)
(* on M or on the orientable double cover; then SPLIT_ROUND).               *)

let P2B_SPLIT_CYL_STATEMENT = new_definition
 `P2B_SPLIT_CYL_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) b s0 x0 u v.
       p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\ x0 IN topspace top /\
       ~collinear {vec 0,u,v} /\ mfd_sectional atlas (g s0) x0 u v = &0
       ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`;;

(* X2 (Prop 9.39 with Cor 9.52 for the class): X0, then the limit is the     *)
(* cylinder model (non-flat at s < 0 by FLAT_FORWARD, lorient passes to the  *)
(* limit, SPLIT_ROUND).  The limit is also smooth up to 0 (rfs_flow_upto, as *)
(* in X0).                                                                   *)

let P2B_CYL_AT_INFINITY_STATEMENT = new_definition
 `P2B_CYL_AT_INFINITY_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) b s0 p pp.
       p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\ p IN topspace top /\
       (!k. pp k IN topspace top) /\
       (!M. ?N. !k. N <= k
                    ==> M < mfd_scalar atlas (g s0) (pp k) *
                            mfd_dist (top,atlas) (g s0) p (pp k) pow 2)
       ==> ?sub q (top':B topology) atlas' g' xl W phi.
              p3_subseq sub /\
              (!k. q k IN topspace top /\
                   mfd_scalar atlas (g s0) (pp (sub k)) <= mfd_scalar atlas (g s0) (q k)) /\
              (!M. ?N. !k. N <= k
                           ==> M < mfd_scalar atlas (g s0) (q k) *
                                   mfd_dist (top,atlas) (g s0) p (q k) pow 2) /\
              p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {s | s < b} g) q (\k. s0)
                                  (\k. mfd_scalar atlas (g s0) (q k)) {s | s <= &0}
                                  (top',atlas') g' xl W phi /\
              (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
              p2b_cyl_model (top',atlas') g'`;;

(* X2s (Cor 9.49 with Cor 9.52 for shrinker flows, MT p. 213): the based     *)
(* limit at MT time -1 on s <= 0 is the cylinder model (X2 at s0 = -1; the   *)
(* Prop 9.46 route uses only that slice), for EVERY sequence pp k at         *)
(* infinity along which R(G(-1)) tends to a limit L > 0 that bounds R(G(-1)) *)
(* up to e outside a compact set (MT p. 212 picks such points with L the     *)
(* limsup of R at infinity; MT Claim 9.51 needs limits at prescribed         *)
(* points): the limit exists along a subsequence at the given points,        *)
(* normalized by R(G(-1))(pp(sub k)), with R(xl,0) = 1, smooth up to 0.      *)
(* With L = sup R this gives the limit at the points q = pp o sub.           *)

let P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT = new_definition
 `P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT (w:B->bool) <=>
    !kappa top atlas (G:real->B->real^3^3) C.
       p2b_ancflow kappa (top,atlas) G (&0) /\ ~compact_space top /\
       (!t x. t < &0 /\ x IN topspace top ==> mfd_rm_norm atlas (G t) x <= C / abs t) /\
       (!t x u v. t < &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 < mfd_sectional atlas (G t) x u v)
       ==> !pp:num->B.
              (!k. pp k IN topspace top) /\
              (!S. compact_in top S ==> ?N. !k. N <= k ==> ~(pp k IN S)) /\
              (?L. &0 < L /\ ((\k. mfd_scalar atlas (G(--(&1))) (pp k)) ---> L) sequentially /\
                   (!e. &0 < e
                        ==> ?S. compact_in top S /\
                                !x. x IN topspace top /\ ~(x IN S)
                                    ==> mfd_scalar atlas (G(--(&1))) x <= L + e))
              ==> ?sub (top':B topology) atlas' g' xl W phi.
                     p3_subseq sub /\
                     p2c_flow_limit_with (\k. rfs_flow_view (top,atlas) {t | t < &0} G)
                       (pp o sub) (\k. --(&1)) (\k. mfd_scalar atlas (G(--(&1))) (pp(sub k)))
                       {s | s <= &0} (top',atlas') g' xl W phi /\
                     mfd_scalar atlas' (g'(&0)) xl = &1 /\
                     (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
                     p2b_cyl_model (top',atlas') g'`;;

(* ------------------------------------------------------------------------- *)
(* S4. Flat forward (a lemma of Part 2B).  Proof: u = R, u_t <= Lap u + 6K   *)
(* u; the first time at which e^(-Lt) u - eta e^(Lt) psi becomes positive    *)
(* (psi of RFA_HARNACK_BARRIER, pc_rfa_hbar), attained in a compact sublevel *)
(* set of psi; the smooth upper barrier q in space (RFA_LLAP_LOCAL_MAX,      *)
(* pc_rfa_lalg), the backward bound in time; RFA_DINI_GRONWALL and the       *)
(* template RFA_MAXP_BARRIER (pc_rfa_maxp), through a general first-bad-time *)
(* lemma (closed bad set in [t1,t2] x K, K compact).                         *)
(* ------------------------------------------------------------------------- *)

(* P2B_REQ_FLAT_FORWARD_STATEMENT is in pc_p2b_kreq (the 11.8 route of       *)
(* pc_p2c_iface uses it).                                                    *)

(* ------------------------------------------------------------------------- *)
(* Route obligations of the splitting part.                                  *)
(* ------------------------------------------------------------------------- *)

(* X0: point picking (MT Lemma 9.37, Cor 9.38), R <= 4 Q k on the picked     *)
(* balls for all earlier times (dR/ds >= 0), compactness, a line in the      *)
(* limit from the segments to p (Thm 5.35), Toponogov splitting at time 0    *)
(* (the theorem CMP_R3_SPLIT of pc_cmp_split, loaded by the proof unit, not  *)
(* an input here), the parallel field stays parallel for s <= 0              *)
(* (RFA_P2B_REQ_SMP_SPLIT_PT of pc_rfa_splitend).  The route inputs are      *)
(* statements proved in other units.                                         *)

let P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT = new_definition
 `P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
    ==> P2B_SPLIT_AT_INFINITY_STATEMENT w`;;

(* SPLIT_ROUND (the split trick): (S0) the orbits of X are geodesics and the *)
(* flow of X is an isometry of every slice, g(s) X does not depend on s;     *)
(* (S2) bounded slices: X0's internals with base points moved along the      *)
(* X-orbits give a limit with two orthogonal parallel fields, flat against R *)
(* = 1 (this needs ANCIENT_COMPACT, X0's own route input), so the shifted    *)
(* flow is a kappa-solution; (S3) its asymptotic soliton (THM_9_11) carries  *)
(* the limit of X and splits globally (h = 2 X(f)); (S4) the soliton leaf is *)
(* a compact round S^2 (R = C e^f, the 2-d clause of                         *)
(* P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT); (S5) a compact leaf L of M         *)
(* (primitives of g(X,.) on simply connected neck regions) and M = L x R;    *)
(* (S6) the leaf flow is round by Hamilton's entropy                         *)
(* (P2B_REQ_S2_ENTROPY_STATEMENT of pc_p2b_s2entreq); (S7) assembly.         *)

let P2B_SPLIT_ROUND_ROUTE_STATEMENT = new_definition
 `P2B_SPLIT_ROUND_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_AT_INFINITY_STATEMENT w /\ P2B_THM_9_11_STATEMENT w /\
    P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
    P2B_REQ_S2_ENTROPY_STATEMENT w
    ==> P2B_SPLIT_ROUND_STATEMENT w`;;

(* X1: RFA_P2B_REQ_SMP_SPLIT_PT at (x0,s0) (each earlier slice flat or       *)
(* locally split; not flat), the kernel line field of Ric is parallel, a     *)
(* global field on M or on the orientable double cover (lorient),            *)
(* SPLIT_ROUND there.                                                        *)

let P2B_SPLIT_CYL_ROUTE_STATEMENT = new_definition
 `P2B_SPLIT_CYL_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_ROUND_STATEMENT w
    ==> P2B_SPLIT_CYL_STATEMENT w`;;

(* X2: X0, non-flatness of the limit at s < 0 (FLAT_FORWARD from R = 1 at  *)
(* time 0), p2b_lorient of the limit (as P2B_KSEP_LIMIT), SPLIT_ROUND on    *)
(* s < 0 and smoothness up to 0.                                             *)

let P2B_CYL_AT_INFINITY_ROUTE_STATEMENT = new_definition
 `P2B_CYL_AT_INFINITY_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_AT_INFINITY_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w /\
    P2B_REQ_FLAT_FORWARD_STATEMENT w
    ==> P2B_CYL_AT_INFINITY_STATEMENT w`;;

(* X2s: as X2 for the forward-extended limits of shrinker flows (curvature  *)
(* bounded by C/|t| on t <= t0 < 0 gives the limit on all of t < 0).        *)

let P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT = new_definition
 `P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_AT_INFINITY_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w /\
    P2B_REQ_FLAT_FORWARD_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
    ==> P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT w`;;

(* FLAT_FORWARD is a leaf of Part 2B: its proof uses RFA_HARNACK_BARRIER     *)
(* (pc_rfa_hbar), so it has no route statement.                              *)

(* The composed chain of the splitting part (THM_9_11 is the main statement  *)
(* of the soliton part; FLAT_FORWARD is a leaf of the splitting part).       *)

let P2B_SPLIT_CHAIN = prove
 (`!w:B->bool.
     P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT w /\ P2B_SPLIT_ROUND_ROUTE_STATEMENT w /\
     P2B_SPLIT_CYL_ROUTE_STATEMENT w /\ P2B_CYL_AT_INFINITY_ROUTE_STATEMENT w /\
     P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT w /\ P2B_REQ_FLAT_FORWARD_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_THM_9_11_STATEMENT w /\
     P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT w /\ P2B_REQ_S2_ENTROPY_STATEMENT w
     ==> P2B_SPLIT_ROUND_STATEMENT w /\ P2B_SPLIT_CYL_STATEMENT w /\
         P2B_CYL_AT_INFINITY_STATEMENT w /\ P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT w /\
         P2B_REQ_FLAT_FORWARD_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_ROUTE_STATEMENT; P2B_SPLIT_ROUND_ROUTE_STATEMENT;
              P2B_SPLIT_CYL_ROUTE_STATEMENT; P2B_CYL_AT_INFINITY_ROUTE_STATEMENT;
              P2B_SHRINKER_CYL_AT_INFINITY_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `P2B_SPLIT_AT_INFINITY_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_SPLIT_ROUND_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_SPLIT_CYL_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_CYL_AT_INFINITY_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The shrinker part.                                                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* V1. kappa-noncollapsed Riemannian manifolds (MT Def 9.41), any N.        *)
(* ------------------------------------------------------------------------- *)

let p2b_rm_noncoll = new_definition
 `p2b_rm_noncoll (kappa:real) (top:B topology,atlas:((B->bool)#(B->real^N))->bool)
                 (g:B->real^N^N) <=>
    !p r. p IN topspace top /\ &0 < r /\
          (!y. y IN mfd_ball (top,atlas) g p r ==> mfd_rm_norm atlas g y <= inv(r pow 2))
          ==> ?v. mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g p r) v /\
                  kappa * r pow dimindex(:N) <= v`;;

(* V3. The asymptotic soliton as Thm 9.11 and Prop 9.32 deliver it: the      *)
(* class on s < 1 with the gradient shrinking soliton equation at EVERY      *)
(* time, Ric + Hess f(s) = g(s) / (2 (1 - s)), i.e. p2b_shrinker for the     *)
(* metric g(s) / (1 - s) (Cor 9.54 needs every time).                        *)

let p2b_sflow = new_definition
 `p2b_sflow (kappa:real) (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
            (g:real->B->real^3^3) (f:real->B->real) <=>
    p2b_ancflow kappa (top,atlas) g (&1) /\
    (!s. s < &1 ==> p2b_shrinker (top,atlas) (\x. inv(&1 - s) %% g s x) (f s))`;;

(* ------------------------------------------------------------------------- *)
(* S1. MT Cor 9.53, general form: every slice has bounded curvature.         *)
(* ------------------------------------------------------------------------- *)

let P2B_COR_9_53_STATEMENT = new_definition
 `P2B_COR_9_53_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) b s.
       p2b_ancflow kappa (top,atlas) g b /\ s < b
       ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g s) x <= K`;;

(* S2. MT Prop 9.46 (dimension 3): no noncompact shrinker slice of positive *)
(* curvature with bounded curvature, kappa-noncollapsed (Def 9.41), with    *)
(* separating necks (p2b_ksep replaces MT's argument: diffeomorphic to     *)
(* R^3, so no embedded RP^2).                                               *)

let P2B_PROP_9_46_STATEMENT = new_definition
 `P2B_PROP_9_46_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:B->real^3^3) f.
       hausdorff_space top /\ connected_space top /\ ~compact_space top /\
       p2b_shrinker (top,atlas) g f /\ mfd_complete (top,atlas) g /\
       (?K. !x. x IN topspace top ==> mfd_rm_norm atlas g x <= K) /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 < mfd_sectional atlas g x u v) /\
       &0 < kappa /\ p2b_rm_noncoll kappa (top,atlas) g /\ p2b_ksep top atlas
       ==> F`;;

(* S3. MT Thm 9.42 with Cor 9.54 in flow form (Thm 9.42 applied at every     *)
(* time): an asymptotic soliton with bounded slices is compact and round at  *)
(* s = 0 or the round cylinder model (or its orientable Z/2 quotient) for    *)
(* all t <= 0 after the shift by 1/2 (scalar curvature 1/(1/2 - t), so 1 at  *)
(* s = 0).                                                                   *)

let P2B_THM_9_42F_STATEMENT = new_definition
 `P2B_THM_9_42F_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) f.
       p2b_sflow kappa (top,atlas) g f /\
       (!s. s < &1 ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g s) x <= K)
       ==> (compact_space top /\ p2b_round (top,atlas) (g(&0))) \/
           p2b_cyl_model (top,atlas) (\t. g(t + &1 / &2))`;;

(* S4. The main statement of the shrinker part: the classification half of   *)
(* P2B_ASYM_SOLITON (the conclusions after the flow limit, the shrinker at s *)
(* = 0 and p2b_ksep, which the soliton part supplies).                       *)

let P2B_SOLITON_CLASS_STATEMENT = new_definition
 `P2B_SOLITON_CLASS_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) f.
       p2b_sflow kappa (top,atlas) g f
       ==> (!s. s < &1 ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g s) x <= K) /\
           p2b_kappa_solution kappa (top,atlas) (\t. g(t + &1 / &2)) /\
           ((compact_space top /\ p2b_round (top,atlas) (g(&0))) \/
            p2b_cyl_model (top,atlas) (\t. g(t + &1 / &2)))`;;

(* ------------------------------------------------------------------------- *)
(* Route obligations of the shrinker part.                                   *)
(* ------------------------------------------------------------------------- *)

(* Cor 9.53 (MT p. 217): a zero plane gives the cylinder (X1, bounded);      *)
(* otherwise unbounded R gives necks at the q k of X2 with R(q k) ->         *)
(* infinity, against Prop 2.19 in the separating form (P2_PROP_2_19_SEP of   *)
(* pc_p3_iface).                                                             *)

let P2B_COR_9_53_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_53_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_CYL_STATEMENT w /\ P2B_CYL_AT_INFINITY_STATEMENT w /\
    P2_PROP_2_19_SEP_STATEMENT w
    ==> P2B_COR_9_53_STATEMENT w`;;

(* Prop 9.46 (MT pp. 209-216): the flow G(t) = abs t Phi^* g of grad f       *)
(* (Section 4.1, ODE package pc_ode_vf), Claims 9.47 (CMP_RICCI_INTEGRAL)    *)
(* and 9.48, (9.21), (9.24), (9.25), f proper, R increasing along grad f;    *)
(* the limit at infinity X2s with Claim 9.51; convex level spheres of area < *)
(* 8 pi and intrinsic curvature < 1/2 (a Gauss equation for level sets);     *)
(* Gauss-Bonnet from Part 4: CM_D7_UNIFORMIZATION (pc_an_beltrami) gives     *)
(* conformal coordinates on the level sphere and CML_GB_INEQ                 *)
(* (pc_cm_lemma122) gives 4 pi <= int K dA.  Harnack puts G in the class     *)
(* (dR/dt >= 0).                                                             *)

let P2B_PROP_9_46_ROUTE_STATEMENT = new_definition
 `P2B_PROP_9_46_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT w /\ P2B_REQ_RFA_HARNACK_STATEMENT w
    ==> P2B_PROP_9_46_STATEMENT w`;;

(* Thm 9.42 in flow form: all slices positive: Prop 9.46 at s = 0 (slice     *)
(* kappa-noncollapsing from the flow and dR/ds >= 0 as in MT Cor 9.54) gives *)
(* compactness, and roundness by P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT; a     *)
(* zero plane at some s0: X1 gives the cylinder up to s0 with singular time  *)
(* 1 from the soliton equation, and complete uniqueness                      *)
(* (P2C_REQ_UNIQ_COMPLETE, proved as RFU_A14, with the cylinder exhaustion)  *)
(* extends it to s < 1.                                                      *)

let P2B_THM_9_42F_ROUTE_STATEMENT = new_definition
 `P2B_THM_9_42F_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_PROP_9_46_STATEMENT w /\ P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT w /\
    P2B_SPLIT_CYL_STATEMENT w /\ P2C_REQ_UNIQ_COMPLETE_STATEMENT w
    ==> P2B_THM_9_42F_STATEMENT w`;;

(* The main statement: Cor 9.53 (bounded slices), Thm 9.42F, and the         *)
(* kappa-solution bookkeeping for the shifted flow (|Rm| <= R on [a,0] by    *)
(* dR/ds >= 0).                                                              *)

let P2B_SOLITON_CLASS_ROUTE_STATEMENT = new_definition
 `P2B_SOLITON_CLASS_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_COR_9_53_STATEMENT w /\ P2B_THM_9_42F_STATEMENT w
    ==> P2B_SOLITON_CLASS_STATEMENT w`;;

(* The composed chain of the shrinker part.                                  *)

let P2B_SHRINK_CHAIN = prove
 (`!w:B->bool.
     P2B_COR_9_53_ROUTE_STATEMENT w /\ P2B_PROP_9_46_ROUTE_STATEMENT w /\
     P2B_THM_9_42F_ROUTE_STATEMENT w /\ P2B_SOLITON_CLASS_ROUTE_STATEMENT w /\
     P2B_SPLIT_CYL_STATEMENT w /\ P2B_CYL_AT_INFINITY_STATEMENT w /\
     P2B_SHRINKER_CYL_AT_INFINITY_STATEMENT w /\ P2_PROP_2_19_SEP_STATEMENT w /\
     P2B_REQ_RFA_HARNACK_STATEMENT w /\ P2B_REQ_RFA_SHRINKER_ROUND_STATEMENT w /\
     P2C_REQ_UNIQ_COMPLETE_STATEMENT w
     ==> P2B_SOLITON_CLASS_STATEMENT w /\ P2B_COR_9_53_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_COR_9_53_ROUTE_STATEMENT; P2B_PROP_9_46_ROUTE_STATEMENT;
              P2B_THM_9_42F_ROUTE_STATEMENT; P2B_SOLITON_CLASS_ROUTE_STATEMENT] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `P2B_COR_9_53_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_PROP_9_46_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `P2B_THM_9_42F_STATEMENT (w:B->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Route obligations of the kappa0 layer (MT Cor 9.44, Prop 9.58, Thm 9.59). *)
(* ------------------------------------------------------------------------- *)

(* COR_9_44: a compact round limit makes M compact and the slices g(t0 - tau *)
(* k) almost round; sec > 0 forward from them (RFA_P2_THM_4_23); Hamilton's  *)
(* pinching R-PINCH3 (P2B_REQ_PINCH_ROUND3_STATEMENT of pc_p2b_pinch3req)    *)
(* gives round slices for t < 0; continuity of the curvature at 0 (smooth    *)
(* extension of rfs_flow_upto) gives g(0).                                   *)

let P2B_COR_9_44_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_44_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_PINCH_ROUND3_STATEMENT w
    ==> P2B_COR_9_44_STATEMENT w`;;

(* Prop 9.58 (MT pp. 220-221; the bound 3/2 on l is used only at the base    *)
(* point): asymptotic solitons at the base points (ASYM_SOLITON_AT, l <=     *)
(* 3/2), not compact round when g(0) is not round (COR_9_44), Cor 9.10, MT   *)
(* Thm 8.1 (FL6) and the scaling of the reduced length (FL7).                *)

let P2B_PROP_9_58_ROUTE_STATEMENT = new_definition
 `P2B_PROP_9_58_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_ASYM_SOLITON_AT_STATEMENT w /\ P2B_COR_9_44_STATEMENT w /\
    P2B_COR_9_10_STATEMENT w /\ P2A_FLOW_THM_8_1_STATEMENT w (:3) /\
    P2A_FLOW_SCALING_STATEMENT w (:3)
    ==> P2B_PROP_9_58_STATEMENT w`;;

(* Thm 9.59 on Tao's route (Prop 3.18.3): the asymptotic soliton has         *)
(* asymptotic volume ratio 0, Bishop-Gromov at times tending to -infinity,   *)
(* and Hamilton's distance distortion (MT Claim 9.61 (1)).                   *)

let P2B_THM_9_59_ROUTE_STATEMENT = new_definition
 `P2B_THM_9_59_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_ASYM_SOLITON_STATEMENT w /\ P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\
    P2C_REQ_DIST_DISTORTION_STATEMENT w
    ==> P2B_THM_9_59_STATEMENT w`;;

(* Lemma 9.65 on Tao's route (Prop 3.18.7 with Cor 3.18.6 = MT Cor 9.62,     *)
(* which also covers compact kappa-solutions): a sequence-limit lemma for    *)
(* kappa-solutions, MT Cor 9.62 (volume ratio and curvature at bounded       *)
(* distance), then the lemma by contradiction (flat limit by the Thm 4.18    *)
(* clause of SMP_SPLIT_PT, FLAT_KNC, volume).  The theorems of the pc_lim    *)
(* units and P2B_KSEP_LIMIT are used as theorems, not inputs.                *)

let P2B_LEMMA_9_65_ROUTE_STATEMENT = new_definition
 `P2B_LEMMA_9_65_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_THM_9_59_STATEMENT w /\ P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\
    P2B_REQ_CMP_BISHOP_GROMOV_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w /\
    P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT w /\ P2B_REQ_FLAT_KNC_STATEMENT w
    ==> P2B_LEMMA_9_65_STATEMENT w`;;

(* ------------------------------------------------------------------------- *)
(* The final slice: MT p. 229 applies Cor 9.53, a statement for t < 0, to    *)
(* the final slice t = 0 of the Thm 9.64 limit.  The closed-end class        *)
(* p2b_ancflow0c (flows on t <= 0, smooth up to 0, no non-flatness clause:   *)
(* X0, X2 and the Cor 9.53 core never use it), X0 and X2 at the picking      *)
(* slice 0 (X0_FINAL, X2_FINAL: the statements of X0 and X2 with this class, *)
(* the views p2b_kview up to 0, base times 0), and Cor 9.53 at the final     *)
(* slice (COR_9_53_FINAL: non-flat only at t = 0).  The same view p2b_kview  *)
(* is used everywhere.                                                       *)
(* ------------------------------------------------------------------------- *)

let p2b_ancflow0c = new_definition
 `p2b_ancflow0c (kappa:real) (top:B topology,atlas:((B->bool)#(B->real^3))->bool)
                (g:real->B->real^3^3) <=>
    &0 < kappa /\ hausdorff_space top /\ connected_space top /\ ~(topspace top = {}) /\
    (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
    (!s. s <= &0 ==> mfd_complete (top,atlas) (g s)) /\
    (!s x u v. s <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
               ==> &0 <= mfd_sectional atlas (g s) x u v) /\
    (!s x dR. s < &0 /\ x IN topspace top /\
              ((\t. mfd_scalar atlas (g t) x) has_real_derivative dR) (atreal s)
              ==> &0 <= dR) /\
    (!r0. rfs_kappa_noncollapsed (p2b_kview (top,atlas) g) kappa r0)`;;

let P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT = new_definition
 `P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p pp.
       p2b_ancflow0c kappa (top,atlas) g /\ p IN topspace top /\
       (!k. pp k IN topspace top) /\
       (!M. ?N. !k. N <= k
                    ==> M < mfd_scalar atlas (g(&0)) (pp k) *
                            mfd_dist (top,atlas) (g(&0)) p (pp k) pow 2)
       ==> ?sub q (top':B topology) atlas' g' xl W phi X.
              p3_subseq sub /\
              (!k. q k IN topspace top /\
                   mfd_scalar atlas (g(&0)) (pp (sub k)) <= mfd_scalar atlas (g(&0)) (q k)) /\
              (!M. ?N. !k. N <= k
                           ==> M < mfd_scalar atlas (g(&0)) (q k) *
                                   mfd_dist (top,atlas) (g(&0)) p (q k) pow 2) /\
              p2c_flow_limit_with (\k. p2b_kview (top,atlas) g) q (\k. &0)
                                  (\k. mfd_scalar atlas (g(&0)) (q k)) {s | s <= &0}
                                  (top',atlas') g' xl W phi /\
              connected_space top' /\
              (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
              (!s. s <= &0 ==> mfd_complete (top',atlas') (g' s)) /\
              (!s y u v. s <= &0 /\ y IN topspace top' /\ ~collinear {vec 0,u,v}
                         ==> &0 <= mfd_sectional atlas' (g' s) y u v) /\
              mfd_scalar atlas' (g'(&0)) xl = &1 /\
              (?K. !s y. s <= &0 /\ y IN topspace top' ==> mfd_rm_norm atlas' (g' s) y <= K) /\
              (!r0. rfs_kappa_noncollapsed (p2b_kview (top',atlas') g') kappa r0) /\
              (!s y dR. s <= &0 /\ y IN topspace top' /\
                        ((\t. mfd_scalar atlas' (g' t) y) has_real_derivative dR) (atreal s)
                        ==> &0 <= dR) /\
              p2b_gsplit (top',atlas') g' {s | s <= &0} X`;;

let P2B_CYL_AT_INFINITY_FINAL_STATEMENT = new_definition
 `P2B_CYL_AT_INFINITY_FINAL_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) p pp.
       p2b_ancflow0c kappa (top,atlas) g /\ p2b_ksep top atlas /\ p IN topspace top /\
       (!k. pp k IN topspace top) /\
       (!M. ?N. !k. N <= k
                    ==> M < mfd_scalar atlas (g(&0)) (pp k) *
                            mfd_dist (top,atlas) (g(&0)) p (pp k) pow 2)
       ==> ?sub q (top':B topology) atlas' g' xl W phi.
              p3_subseq sub /\
              (!k. q k IN topspace top /\
                   mfd_scalar atlas (g(&0)) (pp (sub k)) <= mfd_scalar atlas (g(&0)) (q k)) /\
              (!M. ?N. !k. N <= k
                           ==> M < mfd_scalar atlas (g(&0)) (q k) *
                                   mfd_dist (top,atlas) (g(&0)) p (q k) pow 2) /\
              p2c_flow_limit_with (\k. p2b_kview (top,atlas) g) q (\k. &0)
                                  (\k. mfd_scalar atlas (g(&0)) (q k)) {s | s <= &0}
                                  (top',atlas') g' xl W phi /\
              (!a. a < &0 ==> rfs_flow_upto (top',atlas') a (&0) g') /\
              p2b_cyl_model (top',atlas') g'`;;

let P2B_COR_9_53_FINAL_STATEMENT = new_definition
 `P2B_COR_9_53_FINAL_STATEMENT (w:B->bool) <=>
    !kappa top atlas (g:real->B->real^3^3) x0.
       &0 < kappa /\ hausdorff_space top /\ connected_space top /\
       (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) g) /\
       (!s. s <= &0 ==> mfd_complete (top,atlas) (g s)) /\
       (!s x u v. s <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                  ==> &0 <= mfd_sectional atlas (g s) x u v) /\
       (!s x dR. s < &0 /\ x IN topspace top /\
                 ((\t. mfd_scalar atlas (g t) x) has_real_derivative dR) (atreal s)
                 ==> &0 <= dR) /\
       (!r0. rfs_kappa_noncollapsed (p2b_kview (top,atlas) g) kappa r0) /\
       p2b_ksep top atlas /\ x0 IN topspace top /\ &0 < mfd_scalar atlas (g(&0)) x0
       ==> ?K. !x. x IN topspace top ==> mfd_rm_norm atlas (g(&0)) x <= K`;;

(* The routes of the final slice: X0_FINAL from ANCIENT_COMPACT (the X0      *)
(* proof with the closed-end class); X2_FINAL from X0_FINAL, SPLIT_ROUND and *)
(* FLAT_FORWARD (the X2 argument); COR_9_53_FINAL from X2_FINAL and Prop     *)
(* 2.19 (sep) (the Cor 9.53 core).                                           *)

let P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT = new_definition
 `P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w
    ==> P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT w`;;

let P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT = new_definition
 `P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_AT_INFINITY_FINAL_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w /\
    P2B_REQ_FLAT_FORWARD_STATEMENT w
    ==> P2B_CYL_AT_INFINITY_FINAL_STATEMENT w`;;

let P2B_COR_9_53_FINAL_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_53_FINAL_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_CYL_AT_INFINITY_FINAL_STATEMENT w /\ P2_PROP_2_19_SEP_STATEMENT w
    ==> P2B_COR_9_53_FINAL_STATEMENT w`;;

(* Thm 9.64: Lemma 9.65 bounds R on balls at time 0, KSOL_DRDT backwards,    *)
(* ANCIENT_COMPACT gives the limit, COR_9_53_FINAL its bounded final slice   *)
(* (the theorems of the pc_lim units, P2B_KSEP_LIMIT and                     *)
(* P2BX0_SCALAR_POS_ALL are used as theorems).                               *)

let P2B_THM_9_64_ROUTE_STATEMENT = new_definition
 `P2B_THM_9_64_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_LEMMA_9_65_STATEMENT w /\ P2B_KSOL_DRDT_STATEMENT w /\
    P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_COR_9_53_FINAL_STATEMENT w
    ==> P2B_THM_9_64_STATEMENT w`;;

(* The composed final-slice chain. *)

let P2B_FINAL_CHAIN = prove
 (`!w:B->bool.
     P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT w /\
     P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT w /\
     P2B_COR_9_53_FINAL_ROUTE_STATEMENT w /\
     P2B_REQ_P2C_ANCIENT_COMPACT_STATEMENT w /\ P2B_SPLIT_ROUND_STATEMENT w /\
     P2B_REQ_FLAT_FORWARD_STATEMENT w /\ P2_PROP_2_19_SEP_STATEMENT w
     ==> P2B_COR_9_53_FINAL_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_SPLIT_AT_INFINITY_FINAL_ROUTE_STATEMENT;
              P2B_CYL_AT_INFINITY_FINAL_ROUTE_STATEMENT;
              P2B_COR_9_53_FINAL_ROUTE_STATEMENT] THEN
  MESON_TAC[]);;

(* Cor 9.71 = MT (9.33)-(9.34), the derivative bounds of Thm 9.93 (Shi       *)
(* route): after a time shift and the scaling to R(x,t) = 1, a round slice   *)
(* has grad R = 0, Lap R = 0, abs Ric^2 <= R^2; otherwise Prop 9.58 gives a  *)
(* uniform kappa0, Lemma 9.65 bounds R on the ball at time t, dR/ds >= 0     *)
(* (P2B_KSOL_DRDT, from Hamilton's Harnack inequality) keeps that bound on   *)
(* the ball over [t - 1,t], and Shi's estimate (RFA_C2_SHI_SCALED) bounds    *)
(* the derivatives at (x,t).                                                 *)

let P2B_COR_9_71_ROUTE_STATEMENT = new_definition
 `P2B_COR_9_71_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_LEMMA_9_65_STATEMENT w /\ P2B_PROP_9_58_STATEMENT w
    ==> P2B_COR_9_71_STATEMENT w`;;

(* A5L (MT Thm 9.93 (6)-(7)): a kappa-solution with p2b_ksep all of whose    *)
(* points at all times are centres of eps-necks is the round cylinder.  At   *)
(* each slice s0 < 0 the necks give a tube (APX_A19, pc_apx_chain) whose     *)
(* spheres separate (p2b_ksep), hence two ends, a line (APXT_TWO_ENDS_LINE), *)
(* a parallel unit field (CMPSP_SPLIT_GEN) and a zero plane; X1 makes the    *)
(* flow up to s0 the cylinder model, one-to-one (the Z/2 quotient contains   *)
(* no line); the final slice 0 by continuity of the flow at 0; the model has *)
(* evolving necks of every length.  X1 is the only input.                    *)

let P2B_KAPPA_NECKS_ROUND_L_ROUTE_STATEMENT = new_definition
 `P2B_KAPPA_NECKS_ROUND_L_ROUTE_STATEMENT (w:B->bool) <=>
    P2B_SPLIT_CYL_STATEMENT w
    ==> P2B_KAPPA_NECKS_ROUND_L_FIX_STATEMENT w`;;

(* ========================================================================= *)
(* P2B_ASYM_FROM_PARTS.                                                      *)
(* ========================================================================= *)

let P2B_ASYM_FROM_PARTS = prove
 (`!w:B->bool.
     P2B_THM_9_11_STATEMENT w /\ P2B_KSEP_LIMIT_STATEMENT w /\ P2B_SOLITON_CLASS_STATEMENT w
     ==> P2B_ASYM_SOLITON_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_THM_9_11_STATEMENT; P2B_ASYM_SOLITON_STATEMENT] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                       `xl:B`; `f:real->B->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2b_ksep (top':B topology) (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `P2B_KSEP_LIMIT_STATEMENT (w:B->bool)` THEN
    REWRITE_TAC[P2B_KSEP_LIMIT_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`\k:num. (top:B topology)`;
                               `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
                               `\k:num. (g:real->B->real^3^3)`; `q:num->B`;
                               `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`;
                               `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                               `g':real->B->real^3^3`; `xl:B`; `{s:real | s < &1}`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_sflow kappa (top',atlas') (g':real->B->real^3^3) f` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2b_sflow; p2b_ancflow]; ALL_TAC] THEN
  UNDISCH_TAC `P2B_SOLITON_CLASS_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_SOLITON_CLASS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                             `atlas':((B->bool)#(B->real^3))->bool`;
                             `g':real->B->real^3^3`; `f:real->B->real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `(f:real->B->real) (&0)`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_shrinker")) (concl th))) THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

(* The same at a given base point (THM_9_11_AT, the l <= 3/2 bound passes    *)
(* through), and the based form implies the plain one.                       *)

let P2B_ASYM_AT_FROM_PARTS = prove
 (`!w:B->bool.
     P2B_THM_9_11_AT_STATEMENT w /\ P2B_KSEP_LIMIT_STATEMENT w /\
     P2B_SOLITON_CLASS_STATEMENT w
     ==> P2B_ASYM_SOLITON_AT_STATEMENT w`,
  GEN_TAC THEN
  REWRITE_TAC[P2B_THM_9_11_AT_STATEMENT; P2B_ASYM_SOLITON_AT_STATEMENT] THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`; `p:B`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                                `p:B`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                       `xl:B`; `f:real->B->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2b_ksep (top':B topology) (atlas':((B->bool)#(B->real^3))->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `P2B_KSEP_LIMIT_STATEMENT (w:B->bool)` THEN
    REWRITE_TAC[P2B_KSEP_LIMIT_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`\k:num. (top:B topology)`;
                               `\k:num. (atlas:((B->bool)#(B->real^3))->bool)`;
                               `\k:num. (g:real->B->real^3^3)`; `q:num->B`;
                               `\k. --((tau:num->real) k)`; `\k. inv((tau:num->real) k)`;
                               `top':B topology`; `atlas':((B->bool)#(B->real^3))->bool`;
                               `g':real->B->real^3^3`; `xl:B`; `{s:real | s < &1}`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2b_sflow kappa (top',atlas') (g':real->B->real^3^3) f` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2b_sflow; p2b_ancflow]; ALL_TAC] THEN
  UNDISCH_TAC `P2B_SOLITON_CLASS_STATEMENT (w:B->bool)` THEN
  REWRITE_TAC[P2B_SOLITON_CLASS_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`kappa:real`; `top':B topology`;
                             `atlas':((B->bool)#(B->real^3))->bool`;
                             `g':real->B->real^3^3`; `f:real->B->real`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `(f:real->B->real) (&0)`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_shrinker")) (concl th))) THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_INV_1; MATRIX_CMUL_LID; ETA_AX] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let P2B_ASYM_SOLITON_AT_IMP = prove
 (`!w:B->bool. P2B_ASYM_SOLITON_AT_STATEMENT w ==> P2B_ASYM_SOLITON_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_ASYM_SOLITON_AT_STATEMENT; P2B_ASYM_SOLITON_STATEMENT] THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?p:B. p IN topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                                `p:B`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                       `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                       `xl:B`; `f:B->real`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tau:num->real`; `q:num->B`; `top':B topology`;
                        `atlas':((B->bool)#(B->real^3))->bool`; `g':real->B->real^3^3`;
                        `xl:B`; `f:B->real`] THEN
  ASM_REWRITE_TAC[]);;

