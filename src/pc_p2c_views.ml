(* ========================================================================= *)
(* Unit pc_p2c_views (Part 2C, MT Ch 5 and 11): the vocabulary of Part 2C.   *)
(* Views of generalized Ricci flows (time-dependent manifolds, atlases and   *)
(* metrics on one carrier, as in pc_rfs_geom): regions carrying a Ricci     *)
(* flow, regular views (MT's generalized Ricci flows as the Ch 11 analysis   *)
(* uses them), geometric limits with explicit exhaustion and maps, kappa-    *)
(* solutions after MT Def 9.2, gradient and Laplacian of functions, blow-up  *)
(* sequences of views; kappa-solutions of the P3 vocabulary are kappa-       *)
(* solutions in the sense of MT Def 9.2.  The definitions p2c_vfam,          *)
(* p2c_vflow, p2c_vflow_from, p2c_regular_view, p2c_slice_limit_with,        *)
(* p2c_flow_limit_with and p2c_kappa_sol (and the statements                 *)
(* P2C_HISTORY_REGULAR_STATEMENT and P2C_FLOW_VIEW_REGULAR_STATEMENT) are    *)
(* made in pc_p3_iface, loaded here through pc_p3_route; they are described  *)
(* below.                                                                    *)
(* ========================================================================= *)

needs "src/pc_p3_route.ml";;
needs "src/pc_apx_sep.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* V1. Regions of a view that carry a Ricci flow (generalizes p3_region_flow *)
(* of the P3 vocabulary from histories to arbitrary views): the set W        *)
(* persists over (a,b] and the metrics of the view on W, transported to the  *)
(* atlas of the slice at b, form a Ricci flow on (a,b] smooth up to b.       *)
(* For V = rfs_view hs this is literally p3_region_flow hs W a b.            *)
(* ------------------------------------------------------------------------- *)

(* p2c_vfam: defined in pc_p3_iface. *)

(* p2c_vflow: defined in pc_p3_iface. *)

(* The same with W also open in the slice at a: the transported family is  *)
(* moreover a flow smooth FROM a (MT: an embedding of W x [a,b]).           *)

(* p2c_vflow_from: defined in pc_p3_iface. *)

(* ------------------------------------------------------------------------- *)
(* V2. Regular views (MT's generalized Ricci flows in the form the Ch 11     *)
(* analysis uses): every non-empty slice is a Hausdorff smooth 3-manifold    *)
(* with a Riemannian metric (views of ordinary flows have empty slices off   *)
(* their time set but keep their atlas, so empty slices are exempt), every   *)
(* persisting region is a Ricci flow, smooth from a when W is also open in   *)
(* the slice at a, and the slices have the same smooth structure on         *)
(* persisting sets (the identity is a diffeomorphism between the slice       *)
(* atlases, as in the transition clause p2a_smooth_trans of pc_p2a_defs,     *)
(* needed to compare chart curves across event times).  Histories are        *)
(* regular (P2C_HISTORY_REGULAR, from Lemma                                  *)
(* 14.11), and so are views of ordinary flows smooth from their initial      *)
(* time (P2C_FLOW_VIEW_REGULAR) and maximal extensions at a singular time    *)
(* (P2C_MAXEXT_REGULAR, from Lemma 11.21 and the Seeley extension).          *)
(* ------------------------------------------------------------------------- *)

(* p2c_regular_view: defined in pc_p3_iface. *)

(* ------------------------------------------------------------------------- *)
(* V3. Geometric limits with EXPLICIT exhaustion W and maps phi (the bodies  *)
(* of p3_slice_limit and p3_flow_limit_on with W, phi as parameters).  MT    *)
(* Prop 5.14 keeps the exhaustion and maps of a given time-0 limit, so that  *)
(* the limit flow has exactly the given initial slice (needed for the        *)
(* standard solution and the forward limits near surgery caps).              *)
(* ------------------------------------------------------------------------- *)

(* p2c_slice_limit_with: defined in pc_p3_iface. *)

(* p2c_flow_limit_with: defined in pc_p3_iface. *)

(* ------------------------------------------------------------------------- *)
(* V4. kappa-solutions in the form of MT Def 9.2:                            *)
(* the flow is smooth UP TO time 0 (rfs_flow_upto on (a,0] for every a < 0)  *)
(* instead of being a Ricci flow on (-inf,b) for some b > 0 as in            *)
(* p3_kappa_solution.  Blow-up limits (MT Thm 11.8) are only defined on      *)
(* (-inf,0]; extending them past 0 as Ricci flows needs short-time existence *)
(* on complete noncompact manifolds, which the PDE layer does not provide.   *)
(* p3_kappa_solution implies p2c_kappa_sol (P2C_KAPPA_SOL_WEAKER).           *)
(* ------------------------------------------------------------------------- *)

(* p2c_kappa_sol: defined in pc_p3_iface. *)

(* ------------------------------------------------------------------------- *)
(* V5. Gradient norm and Laplacian of a real function on a manifold, in the *)
(* preferred chart (for the exhaustion functions of the noncompact          *)
(* uniqueness statement P2C_REQ_UNIQ_COMPLETE), and local persistence of    *)
(* small balls (the view form of MT Thm 11.1 hypothesis (5)).               *)
(* ------------------------------------------------------------------------- *)

let p2c_fgrad2 = new_definition
 `p2c_fgrad2 (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (f:A->real) (x:A) =
    lgrad2 (metric_local atlas (chart_at atlas x) g) (f o chart_inv (chart_at atlas x))
           (SND(chart_at atlas x) x)`;;

let p2c_flap = new_definition
 `p2c_flap (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (f:A->real) (x:A) =
    llap (metric_local atlas (chart_at atlas x) g) (f o chart_inv (chart_at atlas x))
         (SND(chart_at atlas x) x)`;;

let p2c_local_persist = new_definition
 `p2c_local_persist (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) (y:A) (s:real) (t:real) <=>
    ?W. y IN W /\ rfs_persists V W s t`;;

(* ------------------------------------------------------------------------- *)
(* V6. Blow-up sequences of VIEWS (the view form of p3_blowup_seq, MT Thm    *)
(* 11.1 (1)-(5)): regular pinched views with time set in [0,inf), base      *)
(* points with Q n = R -> inf, strong (C,eps)-canonical neighbourhoods      *)
(* above 4 Q n before t n, kappa-noncollapsing on scales <= r0 without       *)
(* exemption on the balls B(x n,t n,A Q n^(-1/2)), local                     *)
(* persistence backward for mu / max(Q n, R(y)) (hypothesis (5)).            *)
(* ------------------------------------------------------------------------- *)

let p2c_vblowup_seq = new_definition
 `p2c_vblowup_seq (C:real,eps:real,kappa:real,r0:real,mu:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) (x:num->A) (t:num->real) <=>
    &0 < kappa /\ &0 < r0 /\ &0 < mu /\
    (!n. p2c_regular_view (V n) /\ rfs_pinched (V n) /\
         (!s. s < &0 ==> rfs_vtop (V n) s = discrete_topology {}) /\
         x n IN topspace(rfs_vtop (V n) (t n))) /\
    (!B. ?N. !n. N <= n ==> B < rfs_vscalar (V n) (t n) (x n)) /\
    (!n y s. s <= t n /\ y IN topspace(rfs_vtop (V n) s) /\
             &4 * rfs_vscalar (V n) (t n) (x n) <= rfs_vscalar (V n) s y
             ==> p3_canon_at (V n) C eps y s) /\
    (!A. ?N. !n y. N <= n /\
                   y IN rfs_vball (V n) (t n) (x n)
                          (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                   ==> p3_noncoll_at (V n) kappa r0 y (t n) /\
                       p2c_local_persist (V n) y
                         (t n - mu * inv(max (rfs_vscalar (V n) (t n) (x n))
                                             (rfs_vscalar (V n) (t n) y)))
                         (t n))`;;

let p2c_vblowup_back = new_definition
 `p2c_vblowup_back (kappa:real,r0:real)
    (V:num->(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
            (real->A->real^3^3)) (x:num->A) (t:num->real) (Tb:real) <=>
    !A. ?N. !n. N <= n
                ==> rfs_persists (V n)
                      (rfs_vball (V n) (t n) (x n)
                         (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n)))))
                      (t n - Tb * inv(rfs_vscalar (V n) (t n) (x n))) (t n) /\
                    !s y. t n - Tb * inv(rfs_vscalar (V n) (t n) (x n)) < s /\
                          s <= t n /\
                          y IN rfs_vball (V n) (t n) (x n)
                                 (A * inv(sqrt(rfs_vscalar (V n) (t n) (x n))))
                          ==> p3_noncoll_at (V n) kappa r0 y s`;;

(* ------------------------------------------------------------------------- *)
(* kappa-solutions of the P3 vocabulary (a Ricci flow past time 0) are       *)
(* kappa-solutions after MT Def 9.2.                                         *)
(* ------------------------------------------------------------------------- *)

let P2C_KAPPA_SOL_WEAKER = prove
 (`!kappa (top:B topology) atlas g.
        p3_kappa_solution kappa (top,atlas) g ==> p2c_kappa_sol kappa (top,atlas) g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_kappa_solution; p2c_kappa_sol] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_flow_upto] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    EXISTS_TAC `b:real` THEN
    EXISTS_TAC `\z. (vectorize:real^3^3->real^(3,3)finite_prod)
                     (metric_local atlas (c:(B->bool)#(B->real^3))
                        ((g:real->B->real^3^3)(drop(fstcart z))) (sndcart z))` THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->B->real^3^3)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(B->bool)#(B->real^3)`) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Views of histories.  The parts of                                        *)
(* rfs_view, slices before time 0 are empty, slices separate along neck      *)
(* spheres when the stages do, the backward blow-up condition of the P3      *)
(* vocabulary is that of views, region flows of history views are            *)
(* p3_region_flow, and the limits of the P3 vocabulary are the limits with  *)
(* explicit exhaustion and maps.                                             *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

let P2C_RFS_VIEW_PARTS = prove
 (`!hs:(A)rfs_history.
        rfs_vtop (rfs_view hs) = rfs_top_at hs /\
        rfs_vatlas (rfs_view hs) = rfs_atlas_at hs /\
        rfs_vmetric (rfs_view hs) = rfs_metric_at hs`,
  REWRITE_TAC[rfs_view; rfs_vtop; rfs_vatlas; rfs_vmetric]);;

let P2C_HIST_NEG_EMPTY = prove
 (`!(hs:(A)rfs_history) s. s < &0 ==> rfs_top_at hs s = discrete_topology {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_top_at; rfs_live] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2C_SEP_EMPTY = prove
 (`!atlas. apx_sphere_sep (discrete_topology {}:A topology) atlas`,
  GEN_TAC THEN REWRITE_TAC[apx_sphere_sep; mfd_neck_chart; mfd_param; mfd_diffeo] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; SUBSET_EMPTY; IMAGE_EQ_EMPTY] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; annulus; IN_ELIM_THM; NOT_FORALL_THM] THEN
  EXISTS_TAC `basis 1:real^3` THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let P2C_HIST_SEP_SLICES = prove
 (`!(hs:(A)rfs_history) s.
        rfs_history_ok hs /\
        (!k. k <= hs_count hs ==> apx_sphere_sep (hs_top hs k) (hs_atlas hs k))
        ==> apx_sphere_sep (rfs_top_at hs s) (rfs_atlas_at hs s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_top_at; rfs_atlas_at] THEN
  COND_CASES_TAC THEN REWRITE_TAC[P2C_SEP_EMPTY] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `s:real`] RFS_SLAB) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rfs_live; rfs_horizon]; SIMP_TAC[]]);;

let P2C_BLOWUP_BACK_HIST = prove
 (`!kappa r0 (hs:num->(A)rfs_history) x t Tb.
        p3_blowup_back (kappa,r0) hs x t Tb <=>
        p2c_vblowup_back (kappa,r0) (\n. rfs_view (hs n)) x t Tb`,
  REWRITE_TAC[p3_blowup_back; p2c_vblowup_back]);;

let P2C_VFLOW_HIST = prove
 (`!(hs:(A)rfs_history) W a b. p2c_vflow (rfs_view hs) W a b <=> p3_region_flow hs W a b`,
  REWRITE_TAC[p2c_vflow; p2c_vfam; p3_region_flow; P2C_RFS_VIEW_PARTS]);;

let P2C_SLICE_LIMIT_WITH = prove
 (`!V x t Q (top:B topology) atlas g (xl:B).
        p3_slice_limit V x t Q (top,atlas) g xl <=>
        mfd_complete (top,atlas) g /\
        ?W phi. p2c_slice_limit_with (V:num->(real->A topology)#
                                         (real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3))
                                     x t Q (top,atlas) g xl W phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_slice_limit; p2c_slice_limit_with] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONV_TAC TAUT);;

let P2C_FLOW_LIMIT_ON_WITH = prove
 (`!V x t Q J (top:B topology) atlas g (xl:B).
        p3_flow_limit_on V x t Q J (top,atlas) g xl <=>
        ?W phi. p2c_flow_limit_with (V:num->(real->A topology)#
                                        (real->((A->bool)#(A->real^3))->bool)#
                                        (real->A->real^3^3))
                                    x t Q J (top,atlas) g xl W phi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_flow_limit_on; p2c_flow_limit_with] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONV_TAC TAUT);;

(* ========================================================================= *)
(* Regularity of history views, of views of                                  *)
(* ordinary flows and of maximal extensions (statement constants, proved in  *)
(* pc_p2c_hreg, pc_p2c_fview and pc_p2c_mxr), and the                        *)
(* blow-up sequences of history views as blow-up sequences of views.         *)
(* ========================================================================= *)

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Views.  Histories are regular views (from MT     *)
(* Lemma 14.11 = P3_LEMMA_14_11_STATEMENT, by induction over the events in   *)
(* (a,b] and restriction within slabs), and so are views of ordinary flows.  *)
(* Backward flow lines of a history give local persistence (retained points *)
(* form sets open in both stages).                                           *)

(* P2C_HISTORY_REGULAR_STATEMENT: defined in pc_p3_iface. *)

(* P2C_FLOW_VIEW_REGULAR_STATEMENT: defined in pc_p3_iface. *)

let P2C_HIST_FLOWLINE_PERSIST_STATEMENT = new_definition
 `P2C_HIST_FLOWLINE_PERSIST_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) y s t.
       rfs_history_ok hs /\ s < t /\ p3_flowline hs y s t
       ==> p2c_local_persist (rfs_view hs) y s t`;;

(* Maximal extensions at the horizon are regular (Lemma 11.21 gives the     *)
(* smooth convergence; the time derivatives converge by the Ricci flow       *)
(* equation; the one-sided smooth extension at T is PDE_SEELEY_CORE).        *)

let P2C_MAXEXT_REGULAR_STATEMENT = new_definition
 `P2C_MAXEXT_REGULAR_STATEMENT (u:A->bool) <=>
    !(hs:(A)rfs_history) gl.
       rfs_history_ok hs /\
       open_in (hs_top hs (hs_count hs)) (p3_omega hs) /\
       rfs_limit_metric (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
         (p3_omega hs) (rfs_horizon hs) (hs_metric hs (hs_count hs)) gl
       ==> p2c_regular_view (p3_maxext hs (p3_omega hs) gl)`;;

(* ------------------------------------------------------------------------- *)
(* Blow-up sequences of histories (P3 vocabulary) are blow-up sequences of   *)
(* their views, given the two regularity statements.                         *)
(* ------------------------------------------------------------------------- *)

let P2C_BLOWUP_SEQ_HIST = prove
 (`!(u:A->bool) C eps kappa r0 mu (hs:num->(A)rfs_history) x t.
        P2C_HISTORY_REGULAR_STATEMENT u /\ P2C_HIST_FLOWLINE_PERSIST_STATEMENT u /\
        p3_blowup_seq (C,eps,kappa,r0,mu) hs x t
        ==> p2c_vblowup_seq (C,eps,kappa,r0,mu) (\n. rfs_view (hs n)) x t`,
  REWRITE_TAC[P2C_HISTORY_REGULAR_STATEMENT; P2C_HIST_FLOWLINE_PERSIST_STATEMENT;
              p3_blowup_seq; p2c_vblowup_seq; P2C_RFS_VIEW_PARTS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[P2C_HIST_NEG_EMPTY];
    X_GEN_TAC `A:real` THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `N:num` o SPEC `A:real`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `y:A`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[p3_flowline]) THEN
    REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[p2c_local_persist; rfs_view; rfs_persists] THEN
      EXISTS_TAC `{y:A}` THEN REWRITE_TAC[IN_SING] THEN
      REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC]]);;

