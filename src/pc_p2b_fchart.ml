(* ========================================================================= *)
(* Unit pc_p2b_fchart (Part 2B): the statement P2B_FLOW_CHART_STATEMENT of   *)
(* unit pc_p2b_w920g, proved as P2B_FLOW_CHART: the chart metric and the     *)
(* chart scalar curvature of a Ricci flow, read in the vocabulary of         *)
(* pc_p2b_w3iface (space-time z, backward time tau = drop(sndcart z),        *)
(* time b - tau), are smooth on the space-time chart domain p2bw_cdom c      *)
(* (b - a), and the chart metric is positive definite there.                 *)
(* Generic in N.                                                             *)
(*                                                                           *)
(* Proof: ricci_flow_on gives smoothness of the metric in (t,y) on           *)
(* interval(lift a,lift b) PCROSS (chart image); the scalar curvature is     *)
(* lscalar of the chart metric (MFD_SCALAR_CHART), smooth by                 *)
(* LRG_RICCI_FLOW_ON_CHART and LRG_LSMOOTH_LSCALAR; both are composed with  *)
(* the affine map z -> pastecart (lift b - sndcart z) (fstcart z).          *)
(* ========================================================================= *)

needs "src/pc_p2b_w920g.ml";;
needs "src/pc_lrg_flowsmooth.ml";;

prioritize_real();;
type_invention_error := true;;

(* The space-time chart domain is open and is a product. *)

let P2BX_CDOM_PCROSS = prove
 (`!(c:(A->bool)#(A->real^N)) tmax.
     p2bw_cdom c tmax = IMAGE (SND c) (FST c) PCROSS interval(vec 0,lift tmax)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; FORALL_PASTECART] THEN
  REWRITE_TAC[p2bw_cdom; PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; DROP_VEC; LIFT_DROP]);;

let P2BX_CDOM_OPEN = prove
 (`!(c:(A->bool)#(A->real^N)) tmax.
     open(IMAGE (SND c) (FST c)) ==> open(p2bw_cdom c tmax)`,
  SIMP_TAC[P2BX_CDOM_PCROSS; OPEN_PCROSS; OPEN_INTERVAL]);;

(* The affine change from (space, backward time) to (time, space). *)

let P2BX_FLIP_SMOOTH = prove
 (`!(s:real^(N,1)finite_sum->bool) b.
     open s ==> smooth_map_on s (\z. pastecart (lift b - sndcart z) (fstcart z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`; `\z:real^(N,1)finite_sum. z`;
                   `sndcart:real^(N,1)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`; `\z:real^(N,1)finite_sum. z`;
                   `fstcart:real^(N,1)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART; SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]]);;

let P2BX_FLIP_IMAGE = prove
 (`!(c:(A->bool)#(A->real^N)) a b.
     IMAGE (\z. pastecart (lift b - sndcart z) (fstcart z)) (p2bw_cdom c (b - a))
     SUBSET interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; PASTECART_IN_PCROSS; IN_INTERVAL_1;
              DROP_SUB; LIFT_DROP] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The scalar curvature in (time, chart coordinates) along a Ricci flow. *)

let P2BX_SCALAR_CHART_SMOOTH = prove
 (`!(top:A topology) atlas a b (g:real->A->real^N^N) c.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas
     ==> smooth_map_on (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c))
           (\z. lift(mfd_scalar atlas (g (drop(fstcart z))) (chart_inv c (sndcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `lrg_lsmooth (IMAGE (SND c) (FST c)) a b
                  (\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `lricci_flow (IMAGE (SND c) (FST c)) a b
                  (\t. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t))` THEN
    REWRITE_TAC[lricci_flow; lrg_lsmooth] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift(lscalar
                    ((\t. metric_local atlas (c:(A->bool)#(A->real^N))
                                       ((g:real->A->real^N^N) t)) (drop(fstcart z)))
                    (sndcart z))` THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_LSCALAR; OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPEC `c:(A->bool)#(A->real^N)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `(g:real->A->real^N^N) (drop s)`;
                 `chart_inv (U:A->bool,phi:A->real^N) y`] MFD_SCALAR_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

(* The main theorem. *)

let P2B_FLOW_CHART = prove
 (`!(u:A->bool) (n:N->bool). P2B_FLOW_CHART_STATEMENT u n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[P2B_FLOW_CHART_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`;
                       `c:(A->bool)#(A->real^N)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(p2bw_cdom (c:(A->bool)#(A->real^N)) (b - a))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BX_CDOM_OPEN]; ALL_TAC] THEN
  ABBREV_TAC `h = \z:real^(N,1)finite_sum. pastecart (lift b - sndcart z) (fstcart z)` THEN
  SUBGOAL_THEN `smooth_map_on (p2bw_cdom (c:(A->bool)#(A->real^N)) (b - a))
                  (h:real^(N,1)finite_sum->real^(1,N)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[P2BX_FLIP_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^(N,1)finite_sum->real^(1,N)finite_sum)
                  (p2bw_cdom (c:(A->bool)#(A->real^N)) (b - a))
                SUBSET interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c)`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[P2BX_FLIP_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `open(interval(lift a,lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^(N,1)finite_sum.
                  drop(fstcart((h:real^(N,1)finite_sum->real^(1,N)finite_sum) z)) =
                  b - drop(sndcart z) /\
                  sndcart(h z) = fstcart z`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_SUB;
                                    LIFT_DROP];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o p2bw_cmet atlas c b g =
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
           (metric_local atlas (c:(A->bool)#(A->real^N))
              ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))) o
      (h:real^(N,1)finite_sum->real^(1,N)finite_sum)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bw_cmet] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `(\z. lift(p2bw_cscal atlas c b g z)) =
      (\z. lift(mfd_scalar atlas ((g:real->A->real^N^N) (drop(fstcart z)))
                           (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))) o
      (h:real^(N,1)finite_sum->real^(1,N)finite_sum)`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; p2bw_cscal] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX_SCALAR_CHART_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^(N,1)finite_sum` THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; p2bw_cmet] THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas
                    ((g:real->A->real^N^N) (b - drop(sndcart(z:real^(N,1)finite_sum))))`
    MP_TAC THENL
     [UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                                 (g:real->A->real^N^N)` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ASM_REWRITE_TAC[metric_field] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

