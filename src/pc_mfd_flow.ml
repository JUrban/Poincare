(* ========================================================================= *)
(* pc_mfd_flow: flows of time-dependent vector fields on Hausdorff smooth    *)
(* manifolds.  The field X t (coordinates in the preferred chart, as for     *)
(* mfd_vrep) is smooth on J PCROSS (each chart image) for an open interval   *)
(* J and vanishes off a compact set K.  The flow mfl_flow s t x is the end   *)
(* point at time t of an integral curve on segment[s,t] starting from x at  *)
(* time s (Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 9.48 for *)
(* time-dependent flows and Theorem 9.16 for compact supports).              *)
(* Route: integral curves on intervals (mfl_curve); uniqueness by a clopen   *)
(* argument with ODE_SOLUTION_UNIQUE in charts; a uniform time step on      *)
(* compact time windows from ODE_DOMAIN_UNIFORM_TIME on finitely many chart *)
(* balls covering K; existence on segments by finitely many glued steps;    *)
(* the cocycle law; joint smoothness propagated step by step through chart  *)
(* flows (ODE_FLOW_SMOOTH).  Main results: MFLOW_GEN (the general form),     *)
(* SMT_REQ_MFLOW (the statement SMT_REQ_MFLOW_STATEMENT, defined below) and  *)
(* PDE_REQ_MFLOW (the statement PDE_REQ_MFLOW_STATEMENT of pc_pde_iface).    *)
(*                                                                           *)
(* First: the statement SMT_REQ_MFLOW_STATEMENT, definitions, chart field    *)
(* facts.                                                                    *)
(* ========================================================================= *)

needs "src/pc_pde_iface.ml";;
needs "src/pc_ode_vf.ml";;
needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

(* The statement SMT_REQ_MFLOW_STATEMENT: flows of compactly supported       *)
(* smooth time-dependent vector fields on a Hausdorff manifold.              *)

let SMT_REQ_MFLOW_STATEMENT = new_definition
 `SMT_REQ_MFLOW_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas (X:real->A->real^N) K.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        (!c. c IN atlas
             ==> smooth_map_on ((:real^1) PCROSS IMAGE (SND c) (FST c))
                   (\z. mfd_vrep atlas (X (drop(fstcart z))) c (sndcart z))) /\
        compact_in top K /\
        (!t x. x IN topspace top DIFF K ==> X t x = vec 0)
        ==> ?Phi:real->A->A.
              (!x. x IN topspace top ==> Phi (&0) x = x) /\
              (!t. ?Psi. mfd_diffeo top atlas (topspace top)
                                    top atlas (topspace top) (Phi t) Psi) /\
              (!t x. x IN topspace top DIFF K ==> Phi t x = x) /\
              (!c t x. c IN atlas /\ x IN topspace top /\ Phi t x IN FST c
                       ==> ((\s. SND c (Phi (drop s) x)) has_vector_derivative
                            mfd_vrep atlas (X t) c (SND c (Phi t x)))
                           (at (lift t))) /\
              (!c c'. c IN atlas /\ c' IN atlas
                      ==> smooth_map_on
                            {pastecart (lift t) y |
                               y IN IMAGE (SND c) (FST c) /\
                               Phi t (chart_inv c y) IN FST c'}
                            (\z. SND c' (Phi (drop(fstcart z))
                                             (chart_inv c (sndcart z)))))`;;

(* The chart field of X in the chart c, on time-state points.               *)

let mfl_field = new_definition
 `mfl_field (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N)
            (c:(A->bool)#(A->real^N)) =
    \z:real^(1,N)finite_sum. mfd_vrep atlas (X (drop(fstcart z))) c (sndcart z)`;;

(* The standing hypotheses.                                                  *)

let mfl_hyp = new_definition
 `mfl_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
          (X:real->A->real^N) (J:real^1->bool) (K:A->bool) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\
    open J /\ is_interval J /\
    (!c. c IN atlas
         ==> smooth_map_on (J PCROSS IMAGE (SND c) (FST c)) (mfl_field atlas X c)) /\
    compact_in top K /\
    (!t x. t IN J /\ x IN topspace top DIFF K ==> X (drop t) x = vec 0)`;;

(* Integral curves on an interval L: continuous, with the chart velocity     *)
(* given by X in every chart (derivatives within L).                        *)

let mfl_curve = new_definition
 `mfl_curve (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
            (X:real->A->real^N) (L:real^1->bool) (gamma:real^1->A) <=>
    is_interval L /\
    continuous_map (subtopology euclidean L,top) gamma /\
    (!c t. c IN atlas /\ t IN L /\ gamma t IN FST c
           ==> ((\r. SND c (gamma r)) has_vector_derivative
                mfd_vrep atlas (X (drop t)) c (SND c (gamma t))) (at t within L))`;;

(* The flow from time s to time t.                                           *)

let mfl_flow = new_definition
 `mfl_flow (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
           (X:real->A->real^N) (s:real^1) (t:real^1) (x:A) =
    @y:A. ?gamma. mfl_curve top atlas X (segment[s,t]) gamma /\
                  gamma s = x /\ gamma t = y`;;

let MFL_FIELD_PASTECART = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) c t y.
        mfl_field atlas X c (pastecart t y) = mfd_vrep atlas (X (drop t)) c y`,
  REWRITE_TAC[mfl_field; FSTCART_PASTECART; SNDCART_PASTECART]);;

let MFL_HYP_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K c.
        mfl_hyp top atlas X J K /\ c IN atlas
        ==> open (J PCROSS IMAGE (SND c) (FST c)) /\
            smooth_map_on (J PCROSS IMAGE (SND c) (FST c)) (mfl_field atlas X c) /\
            mfl_field atlas X c continuous_on (J PCROSS IMAGE (SND c) (FST c)) /\
            ode_locally_lipschitz (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))`,
  REWRITE_TAC[mfl_hyp] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open ((J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on ((J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                              (mfl_field atlas (X:real->A->real^N) c)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`mfl_field atlas (X:real->A->real^N) c`;
                 `(J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`]
    ODE_SMOOTH_IMP_LOCALLY_LIPSCHITZ) THEN
  ASM_SIMP_TAC[]);;

(* Pair-free chart facts.                                                     *)

let MFL_CHART_JAC_CHAIN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c1 c2 c3 x v.
        smooth_manifold_atlas top atlas /\ c1 IN atlas /\ c2 IN atlas /\ c3 IN atlas /\
        x IN FST c1 /\ x IN FST c2 /\ x IN FST c3
        ==> chart_jac c2 c3 x (chart_jac c1 c2 x v) = chart_jac c1 c3 x v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c1:(A->bool)#(A->real^N))`; `SND(c1:(A->bool)#(A->real^N))`;
                 `FST(c2:(A->bool)#(A->real^N))`; `SND(c2:(A->bool)#(A->real^N))`;
                 `FST(c3:(A->bool)#(A->real^N))`; `SND(c3:(A->bool)#(A->real^N))`;
                 `x:A`] CHART_JAC_CHAIN) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let MFL_CHART_TRANS_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c c' x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        x IN FST c /\ x IN FST c'
        ==> (chart_trans c c' has_derivative chart_jac c c' x) (at (SND c x)) /\
            linear(chart_jac c c' x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `x:A`] CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN MESON_TAC[has_derivative]);;

let MFL_CHART_IN_TOPSPACE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ x IN FST c
        ==> x IN topspace top`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
  ASM SET_TAC[]);;

(* The transformation law of chart representatives of a vector field.       *)

let MFL_VREP_TRANS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) c c' x.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        x IN FST c /\ x IN FST c'
        ==> mfd_vrep atlas Z c' (SND c' x) =
            chart_jac c c' x (mfd_vrep atlas Z c (SND c x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mfd_vrep] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFL_CHART_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
    CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFL_CHART_JAC_CHAIN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MFL_VREP_ZERO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        y IN IMAGE (SND c) (FST c) /\ Z(chart_inv c y) = vec 0
        ==> mfd_vrep atlas Z c y = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFL_CHART_IN_TOPSPACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[mfd_vrep] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                           (chart_inv (c:(A->bool)#(A->real^N)) y)`;
                 `c:(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] MFL_CHART_TRANS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[LINEAR_0]);;

(* The chain rule for curves, derivatives within a set.                     *)

let MFL_VDERIV_CHAIN_WITHIN = prove
 (`!(u:real^1->real^M) (psi:real^M->real^N) u' D t s.
        (u has_vector_derivative u') (at t within s) /\
        (psi has_derivative D) (at (u t))
        ==> ((\r. psi(u r)) has_vector_derivative D u') (at t within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(D:real^M->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^1->real^M`; `psi:real^M->real^N`;
                 `\x:real^1. drop x % (u':real^M)`; `D:real^M->real^N`; `t:real^1`;
                 `s:real^1->bool`] DIFF_CHAIN_WITHIN) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN; o_DEF] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[LINEAR_CMUL]);;

(* Open sets through charts.                                                 *)

let MFL_CHART_PREIMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c G.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ open G
        ==> open_in top {p | p IN FST c /\ SND c p IN G}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDM_OPEN_IN_PREIMAGE THEN
  EXISTS_TAC `euclidean:(real^N)topology` THEN
  ASM_REWRITE_TAC[OPEN_IN_EUCLIDEAN] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX]);;

let MFL_CHART_IMAGE_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c O.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ open_in top O
        ==> open (IMAGE (SND c) (FST c INTER O))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_SIMP_TAC[]);;

let MFL_CHART_INV_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c.
        smooth_manifold_atlas top atlas /\ c IN atlas
        ==> continuous_map (subtopology euclidean (IMAGE (SND c) (FST c)),top)
                           (chart_inv c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`]
                GRGD_CHART_INV_CONTINUOUS) THEN
  ASM_REWRITE_TAC[PAIR]);;

(* ------------------------------------------------------------------------- *)
(* Integral curves.  Values, restriction to subintervals, change of the      *)
(* curve on its interval, constant curves off K and on single points, and    *)
(* the passage to and from chart solutions of the ODE package.               *)
(* ------------------------------------------------------------------------- *)

let MFL_CURVE_IN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X L gamma t.
        mfl_curve top atlas X L gamma /\ t IN L ==> gamma t IN topspace top`,
  REWRITE_TAC[mfl_curve; continuous_map; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

let MFL_CURVE_SUBSET = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X L L' gamma.
        mfl_curve top atlas X L gamma /\ is_interval L' /\ L' SUBSET L
        ==> mfl_curve top atlas X L' gamma`,
  REWRITE_TAC[mfl_curve] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `L:real^1->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real^1`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `L:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MFL_CURVE_EQ = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X L gamma gamma'.
        mfl_curve top atlas X L gamma /\ (!t. t IN L ==> gamma' t = gamma t)
        ==> mfl_curve top atlas X L gamma'`,
  REWRITE_TAC[mfl_curve] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `gamma:real^1->A` THEN
    ASM_SIMP_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real^1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gamma':real^1->A) t = gamma t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC
   [`\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real^1->A) r)`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MFL_CURVE_CONST = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L x.
        mfl_hyp top atlas X J K /\ is_interval L /\ L SUBSET J /\
        x IN topspace top DIFF K
        ==> mfl_curve top atlas X L (\t. x)`,
  REWRITE_TAC[mfl_hyp; mfl_curve] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real^1`] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_vrep atlas ((X:real->A->real^N) (drop t)) c (SND c (x:A)) = vec 0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MFL_VREP_ZERO THEN EXISTS_TAC `top:A topology` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `K:A->bool`)) (concl th))) THEN
    ASM SET_TAC[];
    REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]]);;

let MFL_CURVE_SING = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X t0 x.
        x IN topspace top ==> mfl_curve top atlas X {t0} (\t. x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[mfl_curve; IS_INTERVAL_SING; CONTINUOUS_MAP_CONST; IN_SING] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[ODE_HAS_VECTOR_DERIVATIVE_WITHIN_SING]);;

(* Integral curves inside a chart are chart solutions, and conversely.       *)

let MFL_CURVE_TO_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L gamma c.
        mfl_hyp top atlas X J K /\ mfl_curve top atlas X L gamma /\ L SUBSET J /\
        c IN atlas /\ (!t. t IN L ==> gamma t IN FST c)
        ==> ode_solution (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c)) L
                         (\t. SND c (gamma t))`,
  REWRITE_TAC[mfl_curve; ode_solution] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(t:real^1) IN J /\ (gamma:real^1->A) t IN FST (c:(A->bool)#(A->real^N))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[PASTECART_IN_PCROSS; FUN_IN_IMAGE; MFL_FIELD_PASTECART]);;

let MFL_CURVE_FROM_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L u c.
        mfl_hyp top atlas X J K /\ c IN atlas /\
        ode_solution (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c)) L u
        ==> mfl_curve top atlas X L (\t. chart_inv c (u t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  SUBGOAL_THEN
   `is_interval L /\
    (!t. t IN L ==> (u:real^1->real^N) t IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))) /\
    (!t. t IN L
         ==> ((u:real^1->real^N) has_vector_derivative
              mfd_vrep atlas ((X:real->A->real^N) (drop t)) c (u t)) (at t within L))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ode_solution (mfl_field atlas (X:real->A->real^N) c)
                   ((J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                   L u` THEN
    SIMP_TAC[ode_solution; PASTECART_IN_PCROSS; MFL_FIELD_PASTECART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfl_curve] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(\t. chart_inv (c:(A->bool)#(A->real^N)) ((u:real^1->real^N) t)) =
                  chart_inv c o u` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[ODE_SOLUTION_CONTINUOUS]; ASM SET_TAC[]];
      MATCH_MP_TAC MFL_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c':(A->bool)#(A->real^N)`; `t:real^1`] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^1->real^N) t IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) ((u:real^1->real^N) t) IN FST c /\
                SND c (chart_inv c (u t)) = u t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\r. SND (c':(A->bool)#(A->real^N))
                       (chart_inv (c:(A->bool)#(A->real^N)) ((u:real^1->real^N) r))) =
                (\r. chart_trans c c' (u r))` SUBST1_TAC THENL
   [REWRITE_TAC[chart_trans]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(X:real->A->real^N) (drop t)`; `c:(A->bool)#(A->real^N)`;
                 `c':(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) ((u:real^1->real^N) t)`]
    MFL_VREP_TRANS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MFL_VDERIV_CHAIN_WITHIN THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) ((u:real^1->real^N) t)`]
    MFL_CHART_TRANS_DERIV) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness of integral curves.  The set of times where two curves agree   *)
(* is open (ODE_SOLUTION_UNIQUE in a chart around a common value) and its    *)
(* complement is open (Hausdorff), so it is all of the connected interval.   *)
(* ------------------------------------------------------------------------- *)

let MFL_OPEN_IN_CURVE_PREIMAGE = prove
 (`!top (g:real^1->A) L U.
        continuous_map (subtopology euclidean L,top) g /\ open_in top U
        ==> open_in (subtopology euclidean L) {r | r IN L /\ g r IN U}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^1->A`; `subtopology euclidean (L:real^1->bool)`;
                 `top:A topology`; `U:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]);;

let MFL_CURVE_AGREE_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L g1 g2 z.
        mfl_hyp top atlas X J K /\
        mfl_curve top atlas X L g1 /\ mfl_curve top atlas X L g2 /\
        L SUBSET J /\ z IN L /\ g1 z = g2 z
        ==> ?d. &0 < d /\ !r. r IN L /\ r IN ball(z,d) ==> g1 r = g2 r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  SUBGOAL_THEN `is_interval(L:real^1->bool) /\
                continuous_map (subtopology euclidean L,top) (g1:real^1->A) /\
                continuous_map (subtopology euclidean L,top) (g2:real^1->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `(g1:real^1->A) z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFL_CURVE_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `?c:(A->bool)#(A->real^N). c IN atlas /\ (g1:real^1->A) z IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((g1:real^1->A) z)` THEN
    MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !r. r IN L /\ r IN ball(z,d)
            ==> (g1:real^1->A) r IN FST (c:(A->bool)#(A->real^N)) /\
                (g2:real^1->A) r IN FST c`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `g1:real^1->A`; `L:real^1->bool`;
                   `FST(c:(A->bool)#(A->real^N))`] MFL_OPEN_IN_CURVE_PREIMAGE) THEN
    MP_TAC(ISPECL [`top:A topology`; `g2:real^1->A`; `L:real^1->bool`;
                   `FST(c:(A->bool)#(A->real^N))`] MFL_OPEN_IN_CURVE_PREIMAGE) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_INTER) THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^1->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^1) IN G` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^1` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `is_interval(L INTER ball(z:real^1,d))` ASSUME_TAC THENL
   [MATCH_MP_TAC IS_INTERVAL_INTER THEN
    ASM_REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:real^1->A.
        mfl_curve top atlas X L g /\
        (!r. r IN L /\ r IN ball(z,d) ==> g r IN FST (c:(A->bool)#(A->real^N)))
        ==> ode_solution (mfl_field atlas X c)
              ((J:real^1->bool) PCROSS IMAGE (SND c) (FST c))
              (L INTER ball(z,d)) (\t. SND c (g t))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_CURVE_TO_CHART THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `L:real^1->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ode_solution (mfl_field atlas (X:real->A->real^N) c)
      ((J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
      (L INTER ball(z,d)) (\t. SND c ((g1:real^1->A) t)) /\
    ode_solution (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
      (L INTER ball(z,d)) (\t. SND c ((g2:real^1->A) t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c:(A->bool)#(A->real^N)`] MFL_HYP_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
     [`mfl_field atlas (X:real->A->real^N) c`;
      `(J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
      `L INTER ball(z:real^1,d)`; `L INTER ball(z:real^1,d)`;
      `\r. SND (c:(A->bool)#(A->real^N)) ((g1:real^1->A) r)`;
      `\r. SND (c:(A->bool)#(A->real^N)) ((g2:real^1->A) r)`; `z:real^1`]
     ODE_SOLUTION_UNIQUE) THEN
  ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; INTER_IDEMPOT] THEN
  DISCH_TAC THEN X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_MESON_TAC[]);;

let MFL_CURVE_UNIQUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L g1 g2 t0.
        mfl_hyp top atlas X J K /\
        mfl_curve top atlas X L g1 /\ mfl_curve top atlas X L g2 /\
        L SUBSET J /\ t0 IN L /\ g1 t0 = g2 t0
        ==> !t. t IN L ==> g1 t = g2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  SUBGOAL_THEN `is_interval(L:real^1->bool) /\
                continuous_map (subtopology euclidean L,top) (g1:real^1->A) /\
                continuous_map (subtopology euclidean L,top) (g2:real^1->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN L /\ (g1:real^1->A) t = g2 t} = topspace(subtopology euclidean L)`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[]] THEN
  MATCH_MP_TAC TOPC_CONNECTED_SPACE_CLOPEN THEN EXISTS_TAC `t0:real^1` THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `L:real^1->bool` CONNECTED_IN_EUCLIDEAN) THEN
    REWRITE_TAC[connected_in; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1];
    SET_TAC[];
    X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `L:real^1->bool`; `g1:real^1->A`; `g2:real^1->A`; `z:real^1`]
      MFL_CURVE_AGREE_LOCAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `L INTER ball(z:real^1,d)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL; IN_INTER; CENTRE_IN_BALL] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g1:real^1->A) z IN topspace top /\ (g2:real^1->A) z IN topspace top /\
                  ~(g1 z = g2 z)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MFL_CURVE_IN]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`(g1:real^1->A) z`; `(g2:real^1->A) z`] o
      GEN_REWRITE_RULE I [hausdorff_space]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `{r | r IN L /\ (g1:real^1->A) r IN U} INTER
                {r | r IN L /\ (g2:real^1->A) r IN V}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN
      MATCH_MP_TAC MFL_OPEN_IN_CURVE_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM];
      UNDISCH_TAC `DISJOINT (U:A->bool) V` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_ELIM_THM] THEN SET_TAC[]]]);;

(* Two curves on intervals inside J that agree at one time agree on the     *)
(* intersection.                                                             *)

let MFL_CURVE_UNIQUE2 = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L1 L2 g1 g2 t0.
        mfl_hyp top atlas X J K /\
        mfl_curve top atlas X L1 g1 /\ mfl_curve top atlas X L2 g2 /\
        L1 SUBSET J /\ L2 SUBSET J /\ t0 IN L1 /\ t0 IN L2 /\ g1 t0 = g2 t0
        ==> !t. t IN L1 INTER L2 ==> g1 t = g2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MFL_CURVE_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                        `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                        `t0:real^1`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  SUBGOAL_THEN `is_interval((L1:real^1->bool) INTER L2)` ASSUME_TAC THENL
   [MATCH_MP_TAC IS_INTERVAL_INTER THEN ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `L1:real^1->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `L2:real^1->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing two integral curves on closed intervals that meet, and agree at a  *)
(* common time (hence on the whole intersection).                            *)
(* ------------------------------------------------------------------------- *)

let MFL_CURVE_GLUE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L1 L2 g1 g2 r.
        mfl_hyp top atlas X J K /\
        mfl_curve top atlas X L1 g1 /\ mfl_curve top atlas X L2 g2 /\
        closed L1 /\ closed L2 /\ L1 UNION L2 SUBSET J /\
        r IN L1 /\ r IN L2 /\ g1 r = g2 r
        ==> ?g. mfl_curve top atlas X (L1 UNION L2) g /\
                (!t. t IN L1 ==> g t = g1 t) /\ (!t. t IN L2 ==> g t = g2 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. t IN L1 INTER L2 ==> (g1:real^1->A) t = g2 t` ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_CURVE_UNIQUE2 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                          `r:real^1`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g = \t. if t IN L1 then (g1:real^1->A) t else g2 t` THEN
  SUBGOAL_THEN `(!t. t IN L1 ==> (g:real^1->A) t = g1 t) /\
                (!t. t IN L2 ==> (g:real^1->A) t = g2 t)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN CONJ_TAC THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_INTER];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^1->A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfl_curve top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N)
                          L1 (g:real^1->A) /\ mfl_curve top atlas X L2 g`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MFL_CURVE_EQ THENL
     [EXISTS_TAC `g1:real^1->A`; EXISTS_TAC `g2:real^1->A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_interval(L1:real^1->bool) /\ is_interval(L2:real^1->bool) /\
                continuous_map (subtopology euclidean L1,top) (g:real^1->A) /\
                continuous_map (subtopology euclidean L2,top) (g:real^1->A)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `~((L1:real^1->bool) INTER L2 = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfl_curve] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ODE_IS_INTERVAL_UNION THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(INST_TYPE [`:real^1->bool`,`:K`] PASTING_LEMMA_CLOSED) THEN
    MAP_EVERY EXISTS_TAC [`\i:real^1->bool. (g:real^1->A)`; `\i:real^1->bool. i`;
                          `{L1:real^1->bool,L2}`] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                EXISTS_IN_INSERT; SUBTOPOLOGY_SUBTOPOLOGY;
                TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; IN_UNION] THEN
    SUBGOAL_THEN `((L1:real^1->bool) UNION L2) INTER L1 = L1 /\
                  ((L1:real^1->bool) UNION L2) INTER L2 = L2`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSED_SUBSET; SUBSET_UNION] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real^1`] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_INTERVAL_UNION THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; DISCH_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[mfl_curve]) THEN ASM_MESON_TAC[];
      ONCE_REWRITE_TAC[UNION_COMM] THEN
      MATCH_MP_TAC ODE_HAS_VECTOR_DERIVATIVE_INTERVAL_UNION THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; DISCH_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[mfl_curve]) THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Chart flows give integral curves; a uniform time step on a compact time   *)
(* window Tw inside J (ODE_DOMAIN_UNIFORM_TIME on finitely many chart balls  *)
(* covering K, and the margin of Tw in J); local existence of integral       *)
(* curves on cball(t1,e) from any point at any time t1 in Tw.                *)
(* ------------------------------------------------------------------------- *)

let MFL_LOCAL_CURVE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K c t1 y1.
        mfl_hyp top atlas X J K /\ c IN atlas /\ t1 IN J /\
        y1 IN IMAGE (SND c) (FST c)
        ==> open(ode_maxint (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                            (pastecart t1 y1)) /\
            is_interval(ode_maxint (mfl_field atlas X c)
                          (J PCROSS IMAGE (SND c) (FST c)) (pastecart t1 y1)) /\
            t1 IN ode_maxint (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                             (pastecart t1 y1) /\
            ode_maxint (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                       (pastecart t1 y1) SUBSET J /\
            (!t. t IN ode_maxint (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                                 (pastecart t1 y1)
                 ==> ode_flow (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c)) t
                              (pastecart t1 y1) IN IMAGE (SND c) (FST c)) /\
            ode_flow (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c)) t1
                     (pastecart t1 y1) = y1 /\
            mfl_curve top atlas X
              (ode_maxint (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                          (pastecart t1 y1))
              (\t. chart_inv c (ode_flow (mfl_field atlas X c)
                                  (J PCROSS IMAGE (SND c) (FST c)) t (pastecart t1 y1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c:(A->bool)#(A->real^N)`] MFL_HYP_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfl_field atlas (X:real->A->real^N) c`;
                 `(J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                 `pastecart (t1:real^1) (y1:real^N)`] ODE_MAXIMAL_SOLUTION) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ODE_MAXINT_SUBSET_TIMES] THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^1` o check (is_forall o concl)) THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS];
    MATCH_MP_TAC MFL_CURVE_FROM_CHART THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[]]);;

let MFL_UNIFORM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K Tw.
        mfl_hyp top atlas X J K /\ compact Tw /\ Tw SUBSET J
        ==> ?e. &0 < e /\
                (!t1 t. t1 IN Tw /\ dist(t,t1) <= e ==> t IN J) /\
                (!x. x IN K
                     ==> ?c. c IN atlas /\ x IN FST c /\
                             !t1 t. t1 IN Tw /\ dist(t,t1) <= e
                                    ==> t IN ode_maxint (mfl_field atlas X c)
                                               (J PCROSS IMAGE (SND c) (FST c))
                                               (pastecart t1 (SND c x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  SUBGOAL_THEN `?e0. &0 < e0 /\
                     !t1 t. t1 IN Tw /\ dist(t,t1) <= e0 ==> (t:real^1) IN J`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Tw:real^1->bool`; `(:real^1) DIFF J`] SEPARATE_COMPACT_CLOSED) THEN
    ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
    EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MAP_EVERY X_GEN_TAC [`t1:real^1`; `t:real^1`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "sep" (MP_TAC o SPECL [`t1:real^1`; `t:real^1`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]; ALL_TAC]) THEN
    MP_TAC(ISPECL [`t:real^1`; `t1:real^1`] DIST_SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN K
          ==> ?(c:(A->bool)#(A->real^N)) r e.
                      c IN atlas /\ x IN FST c /\ &0 < r /\
                      cball(SND c x,r) SUBSET IMAGE (SND c) (FST c) /\ &0 < e /\
                      !z t. z IN (Tw:real^1->bool) PCROSS cball(SND c x,r) /\
                            abs(drop t - drop(fstcart z)) <= e
                            ==> t IN ode_maxint (mfl_field atlas (X:real->A->real^N) c)
                                       ((J:real^1->bool) PCROSS IMAGE (SND c) (FST c)) z`
  MP_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `?c:(A->bool)#(A->real^N). c IN atlas /\ (x:A) IN FST c`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
      MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `c:(A->bool)#(A->real^N)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `c:(A->bool)#(A->real^N)`] MFL_HYP_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `SND (c:(A->bool)#(A->real^N)) x` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ODE_DOMAIN_UNIFORM_TIME THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_CBALL; PCROSS_MONO];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:A->(A->bool)#(A->real^N)` (X_CHOOSE_THEN `R:A->real`
    (X_CHOOSE_THEN `E:A->real` (LABEL_TAC "data")))) THEN
  ABBREV_TAC
   `Ob = \x:A. {p | p IN FST((C:A->(A->bool)#(A->real^N)) x) /\
                    SND(C x) p IN ball(SND(C x) x,(R:A->real) x)}` THEN
  SUBGOAL_THEN
   `?Fs. FINITE Fs /\ Fs SUBSET K /\ K SUBSET UNIONS (IMAGE (Ob:A->A->bool) Fs)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `IMAGE (Ob:A->A->bool) K` o CONJUNCT2 o
      GEN_REWRITE_RULE I [compact_in]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      CONJ_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "data" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(x:A) IN K`))) THEN
      EXPAND_TAC "Ob" THENL
       [MATCH_MP_TAC MFL_CHART_PREIMAGE_OPEN THEN
        EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN
        ASM_REWRITE_TAC[OPEN_BALL];
        EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:(A->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`Ob:A->A->bool`; `K:A->bool`; `V:(A->bool)->bool`]
      FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `Fs:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = inf ((e0:real) INSERT IMAGE (E:A->real) Fs)` THEN
  SUBGOAL_THEN `&0 < e /\ e <= e0 /\ !x:A. x IN Fs ==> e <= E x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN
    MP_TAC(ISPEC `(e0:real) INSERT IMAGE (E:A->real) Fs` INF_FINITE) THEN
    MP_TAC(ISPECL [`(e0:real) INSERT IMAGE (E:A->real) Fs`; `&0`] REAL_LT_INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
    DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "data" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t1:real^1`; `t:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t1:real^1` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x1:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:A. x IN Fs /\ (x1:A) IN (Ob:A->A->bool) x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `K SUBSET UNIONS (IMAGE (Ob:A->A->bool) Fs)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "data" (MP_TAC o SPEC `x:A`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x1:A) IN Ob (x:A)` THEN EXPAND_TAC "Ob" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `(C:A->(A->bool)#(A->real^N)) x` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t1:real^1`; `t:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `ode_maxint:(real^(1,N)finite_sum->real^N)->(real^(1,N)finite_sum->bool)->real^(1,N)finite_sum->real^1->bool`)) (concl th) &&
    is_forall (concl th))) THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; GSYM DIST_1] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e:real` THEN ASM_SIMP_TAC[]]);;

let MFL_LOCAL_EXISTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K Tw e.
        mfl_hyp top atlas X J K /\ &0 < e /\
        (!t1 t. t1 IN Tw /\ dist(t,t1) <= e ==> t IN J) /\
        (!x. x IN K
             ==> ?c. c IN atlas /\ x IN FST c /\
                     !t1 t. t1 IN Tw /\ dist(t,t1) <= e
                            ==> t IN ode_maxint (mfl_field atlas X c)
                                       (J PCROSS IMAGE (SND c) (FST c))
                                       (pastecart t1 (SND c x)))
        ==> !t1 x1. t1 IN Tw /\ x1 IN topspace top
                    ==> ?gamma. mfl_curve top atlas X (cball(t1,e)) gamma /\
                                gamma t1 = x1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`t1:real^1`; `x1:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `is_interval(cball(t1:real^1,e)) /\ cball(t1,e) SUBSET J /\
                t1 IN cball(t1,e) /\ (t1:real^1) IN J`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CBALL; SUBSET; IN_CBALL; DIST_REFL] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[DIST_SYM]; FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `t1:real^1` THEN ASM_SIMP_TAC[DIST_REFL; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x1:A) IN K` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x1:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `c:(A->bool)#(A->real^N)`; `t1:real^1`;
                   `SND (c:(A->bool)#(A->real^N)) x1`] MFL_LOCAL_CURVE) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN STRIP_TAC THEN
    EXISTS_TAC
     `\t. chart_inv (c:(A->bool)#(A->real^N))
            (ode_flow (mfl_field atlas (X:real->A->real^N) c)
               ((J:real^1->bool) PCROSS IMAGE (SND c) (FST c)) t
               (pastecart t1 (SND c (x1:A))))` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MFL_CURVE_SUBSET THEN
    EXISTS_TAC `ode_maxint (mfl_field atlas (X:real->A->real^N) c)
                  ((J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                  (pastecart t1 (SND c (x1:A)))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_CBALL] THEN
    ASM_MESON_TAC[DIST_SYM];
    EXISTS_TAC `\t:real^1. (x1:A)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MFL_CURVE_CONST THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[IN_DIFF]]);;

(* ------------------------------------------------------------------------- *)
(* Induction along a segment in steps of length e; existence of integral     *)
(* curves on segments; the flow and its basic properties (characterization   *)
(* by any curve, identity at equal times, values in the space, the cocycle   *)
(* law, identity off K, the time derivative in charts).                      *)
(* ------------------------------------------------------------------------- *)

let MFL_SEGMENT_INDUCT = prove
 (`!(P:real^1->bool) s t e.
        &0 < e /\ P s /\
        (!r1 r. r IN segment[s,t] /\ r1 IN segment[s,r] /\ dist(r1,r) <= e /\ P r1
                ==> P r)
        ==> !r. r IN segment[s,t] ==> P r`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step"))) THEN
  SUBGOAL_THEN `!n r. r IN segment[s,t] /\ dist(s,r) <= &n * e ==> (P:real^1->bool) r`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REWRITE_TAC[REAL_MUL_LZERO; DIST_LE_0] THEN ASM_MESON_TAC[];
      POP_ASSUM(LABEL_TAC "ih")] THEN
    X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN
    ABBREV_TAC `r1:real^1 = s + (&n / (&n + &1)) % (r - s)` THEN
    SUBGOAL_THEN `&0 <= &n / (&n + &1) /\ &n / (&n + &1) <= &1 /\
                  &1 - &n / (&n + &1) = inv(&n + &1)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_FIELD `&0 < x + &1 ==> &1 - x / (x + &1) = inv(x + &1)`) THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(s:real^1,r1) = (&n / (&n + &1)) * dist(s,r) /\
                  dist(r1:real^1,r) = inv(&n + &1) * dist(s,r)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r1" THEN REWRITE_TAC[dist] THEN
      REWRITE_TAC[VECTOR_ARITH `s - (s + u % (r - s)):real^N = u % (s - r)`;
                  VECTOR_ARITH `(s + u % (r - s)) - r:real^N = (&1 - u) % (s - r)`] THEN
      ASM_REWRITE_TAC[NORM_MUL] THEN
      SUBGOAL_THEN `&0 <= inv(&n + &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(s:real^1,r) <= (&n + &1) * e` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_SUC]; ALL_TAC] THEN
    SUBGOAL_THEN `(r1:real^1) IN segment[s,r]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&n / (&n + &1)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "r1" THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "step" MATCH_MP_TAC THEN EXISTS_TAC `r1:real^1` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n + &1) * ((&n + &1) * e)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_INV THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MATCH_MP_TAC(REAL_FIELD `&0 < x + &1 ==> inv(x + &1) * ((x + &1) * e) = e`) THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "ih" MATCH_MP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `segment[s:real^1,r] SUBSET segment[s,t]` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT];
        ASM SET_TAC[]];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&n / (&n + &1)) * ((&n + &1) * e)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        MATCH_MP_TAC(REAL_FIELD `&0 < x + &1 ==> (x / (x + &1)) * ((x + &1) * e) = x * e`) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num` o SPEC `dist(s:real^1,r)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* Integral curves on segments, by the uniform step and gluing.            *)

let MFL_EXISTS_SEGMENT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t x.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J /\ x IN topspace top
        ==> ?gamma. mfl_curve top atlas X (segment[s,t]) gamma /\ gamma s = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET J` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_MESON_TAC[mfl_hyp; IS_INTERVAL_CONVEX_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `segment[s:real^1,t]`] MFL_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `segment[s:real^1,t]`; `e:real`] MFL_LOCAL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "loc") THEN
  MP_TAC(ISPECL
   [`\r:real^1. ?gamma. mfl_curve top (atlas:((A->bool)#(A->real^N))->bool)
                          (X:real->A->real^N) (segment[s,r]) gamma /\ gamma s = (x:A)`;
    `s:real^1`; `t:real^1`; `e:real`] MFL_SEGMENT_INDUCT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_REFL] THEN CONJ_TAC THENL
     [EXISTS_TAC `\t:real^1. (x:A)` THEN ASM_SIMP_TAC[MFL_CURVE_SING];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`r1:real^1`; `r:real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `g1:real^1->A` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `segment[s:real^1,r] SUBSET segment[s,t]` ASSUME_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r1:real^1) IN segment[s,t] /\ (g1:real^1->A) r1 IN topspace top`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MFL_CURVE_IN THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                            `segment[s:real^1,r1]`] THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o SPECL [`r1:real^1`; `(g1:real^1->A) r1`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(X_CHOOSE_THEN `g2:real^1->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[r1:real^1,r] SUBSET cball(r1,e)` ASSUME_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      ASM_SIMP_TAC[CONVEX_CBALL; CENTRE_IN_CBALL; REAL_LT_IMP_LE; IN_CBALL; DIST_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `segment[s:real^1,r1]`; `segment[r1:real^1,r]`;
                   `g1:real^1->A`; `g2:real^1->A`; `r1:real^1`] MFL_CURVE_GLUE) THEN
    ASM_SIMP_TAC[UNION_SEGMENT; CLOSED_SEGMENT; ENDS_IN_SEGMENT] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `cball(r1:real^1,e)` THEN
      ASM_REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_SEGMENT];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ENDS_IN_SEGMENT];
    DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN REWRITE_TAC[ENDS_IN_SEGMENT]]);;

(* The flow is read off any integral curve through the initial point.      *)

let MFL_FLOW_CURVE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K L gamma s t.
        mfl_hyp top atlas X J K /\ mfl_curve top atlas X L gamma /\ L SUBSET J /\
        s IN L /\ t IN L
        ==> mfl_flow top atlas X s t (gamma s) = gamma t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET L` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_MESON_TAC[mfl_curve; IS_INTERVAL_CONVEX_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET J /\
                mfl_curve top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N)
                          (segment[s:real^1,t]) (gamma:real^1->A)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MFL_CURVE_SUBSET THEN EXISTS_TAC `L:real^1->bool` THEN
    ASM_REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[mfl_flow] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:real^1->A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `segment[s:real^1,t]`; `g:real^1->A`; `gamma:real^1->A`;
                   `s:real^1`] MFL_CURVE_UNIQUE) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[ENDS_IN_SEGMENT];
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `gamma:real^1->A` THEN
    ASM_REWRITE_TAC[]]);;

let MFL_FLOW_EXISTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t x.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J /\ x IN topspace top
        ==> ?gamma. mfl_curve top atlas X (segment[s,t]) gamma /\ gamma s = x /\
                    mfl_flow top atlas X s t x = gamma t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `s:real^1`; `t:real^1`; `x:A`] MFL_EXISTS_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:real^1->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFL_FLOW_CURVE THEN
  MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`; `segment[s:real^1,t]`] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
  ASM_MESON_TAC[mfl_hyp; IS_INTERVAL_CONVEX_1]);;

let MFL_FLOW_IN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t x.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J /\ x IN topspace top
        ==> mfl_flow top atlas X s t x IN topspace top`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `s:real^1`; `t:real^1`; `x:A`] MFL_FLOW_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFL_CURVE_IN THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                        `segment[s:real^1,t]`] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

let MFL_FLOW_REFL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s x.
        mfl_hyp top atlas X J K /\ s IN J /\ x IN topspace top
        ==> mfl_flow top atlas X s s x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `{s:real^1}`; `\t:real^1. (x:A)`; `s:real^1`; `s:real^1`]
    MFL_FLOW_CURVE) THEN
  ASM_SIMP_TAC[MFL_CURVE_SING; IN_SING; SING_SUBSET]);;

let MFL_FLOW_OFFK = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t x.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J /\ x IN topspace top DIFF K
        ==> mfl_flow top atlas X s t x = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET J` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_MESON_TAC[mfl_hyp; IS_INTERVAL_CONVEX_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `segment[s:real^1,t]`; `\r:real^1. (x:A)`; `s:real^1`; `t:real^1`]
    MFL_FLOW_CURVE) THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC MFL_CURVE_CONST THEN
  MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
  ASM_REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_SEGMENT]);;

(* The cocycle law, by gluing the curves on segment[s,r] and segment[r,t]. *)

let MFL_FLOW_COCYCLE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s r t x.
        mfl_hyp top atlas X J K /\ s IN J /\ r IN J /\ t IN J /\ x IN topspace top
        ==> mfl_flow top atlas X r t (mfl_flow top atlas X s r x) =
            mfl_flow top atlas X s t x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[s:real^1,r] SUBSET J /\ segment[r:real^1,t] SUBSET J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_MESON_TAC[mfl_hyp; IS_INTERVAL_CONVEX_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `s:real^1`; `r:real^1`; `x:A`] MFL_FLOW_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^1->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g1:real^1->A) r IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_CURVE_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                          `segment[s:real^1,r]`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `r:real^1`; `t:real^1`; `(g1:real^1->A) r`] MFL_FLOW_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^1->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `segment[s:real^1,r]`; `segment[r:real^1,t]`;
                 `g1:real^1->A`; `g2:real^1->A`; `r:real^1`] MFL_CURVE_GLUE) THEN
  ASM_REWRITE_TAC[CLOSED_SEGMENT; ENDS_IN_SEGMENT; UNION_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `segment[s:real^1,r] UNION segment[r:real^1,t]`; `g:real^1->A`;
                 `s:real^1`; `t:real^1`] MFL_FLOW_CURVE) THEN
  ASM_REWRITE_TAC[UNION_SUBSET; IN_UNION; ENDS_IN_SEGMENT] THEN
  ASM_SIMP_TAC[ENDS_IN_SEGMENT]);;

(* The time derivative of the flow in a chart.                              *)

let MFL_FLOW_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K c s t x.
        mfl_hyp top atlas X J K /\ c IN atlas /\ s IN J /\ t IN J /\
        x IN topspace top /\ mfl_flow top atlas X s t x IN FST c
        ==> ((\r. SND c (mfl_flow top atlas X s r x)) has_vector_derivative
             mfd_vrep atlas (X (drop t)) c (SND c (mfl_flow top atlas X s t x)))
            (at t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x1 = mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                     (X:real->A->real^N) s t (x:A)` THEN
  SUBGOAL_THEN `(x1:A) IN topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "x1" THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `{t:real^1}`] MFL_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_SING; SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `{t:real^1}`; `e:real`] MFL_LOCAL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `x1:A`]) THEN
  ASM_REWRITE_TAC[IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cball(t:real^1,e) SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `J:real^1->bool`)) (concl th) && is_forall (concl th))) THEN
    EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[IN_SING] THEN
    ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN ball(t:real^1,e)
                    ==> mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                          (X:real->A->real^N) s r (x:A) = (g:real^1->A) r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(r:real^1) IN cball(t,e) /\ t IN cball(t,e)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `s:real^1`; `t:real^1`; `r:real^1`; `x:A`] MFL_FLOW_COCYCLE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(g:real^1->A) t = x1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFL_FLOW_CURVE THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`; `cball(t:real^1,e)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC
   [`\r. SND (c:(A->bool)#(A->real^N)) ((g:real^1->A) r)`; `e:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^1->A) t IN FST (c:(A->bool)#(A->real^N))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `mfl_curve top (atlas:((A->bool)#(A->real^N))->bool)
                 (X:real->A->real^N) (cball(t,e)) g` THEN
  REWRITE_TAC[mfl_curve] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `t:real^1`] o
             CONJUNCT2 o CONJUNCT2) THEN
  ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET)) THEN
  DISCH_THEN(MP_TAC o SPEC `ball(t:real^1,e)`) THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; has_vector_derivative] THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_WITHIN_OPEN; OPEN_BALL; CENTRE_IN_BALL]);;

(* ------------------------------------------------------------------------- *)
(* The flow in a chart is the chart flow of the ODE package; smoothness      *)
(* predicates for the flow at a fixed time (mfl_psmooth) and jointly in time *)
(* and space near a time (mfl_jsmooth); smooth auxiliary maps; the base case *)
(* at the initial time and the passage from joint to fixed time smoothness.  *)
(* ------------------------------------------------------------------------- *)

let MFL_FLOW_CHART = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K c t1 y1 t.
        mfl_hyp top atlas X J K /\ c IN atlas /\ t1 IN J /\
        y1 IN IMAGE (SND c) (FST c) /\
        t IN ode_maxint (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                        (pastecart t1 y1)
        ==> ode_flow (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c)) t
                     (pastecart t1 y1) IN IMAGE (SND c) (FST c) /\
            t IN J /\
            mfl_flow top atlas X t1 t (chart_inv c y1) =
            chart_inv c (ode_flow (mfl_field atlas X c) (J PCROSS IMAGE (SND c) (FST c))
                                  t (pastecart t1 y1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c:(A->bool)#(A->real^N)`; `t1:real^1`; `y1:real^N`] MFL_LOCAL_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `ode_maxint (mfl_field atlas (X:real->A->real^N) c)
                    ((J:real^1->bool) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                    (pastecart t1 (y1:real^N))`;
                 `\t. chart_inv (c:(A->bool)#(A->real^N))
                        (ode_flow (mfl_field atlas (X:real->A->real^N) c)
                           ((J:real^1->bool) PCROSS IMAGE (SND c) (FST c)) t
                           (pastecart t1 (y1:real^N)))`;
                 `t1:real^1`; `t:real^1`] MFL_FLOW_CURVE) THEN
  ASM_REWRITE_TAC[]);;

(* Smoothness predicates.                                                    *)

let mfl_psmooth = new_definition
 `mfl_psmooth (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
              (X:real->A->real^N) (s:real^1) (t:real^1) <=>
    !c c' y0. c IN atlas /\ c' IN atlas /\ y0 IN IMAGE (SND c) (FST c) /\
              mfl_flow top atlas X s t (chart_inv c y0) IN FST c'
              ==> ?W. open W /\ y0 IN W /\
                      (!y. y IN W
                           ==> y IN IMAGE (SND c) (FST c) /\
                               mfl_flow top atlas X s t (chart_inv c y) IN FST c') /\
                      smooth_map_on W (\y. SND c' (mfl_flow top atlas X s t (chart_inv c y)))`;;

let mfl_jsmooth = new_definition
 `mfl_jsmooth (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
              (X:real->A->real^N) (J:real^1->bool) (s:real^1) (t0:real^1) <=>
    !c c' y0. c IN atlas /\ c' IN atlas /\ y0 IN IMAGE (SND c) (FST c) /\
              mfl_flow top atlas X s t0 (chart_inv c y0) IN FST c'
              ==> ?W. open W /\ pastecart t0 y0 IN W /\
                      (!t y. pastecart t y IN W
                             ==> t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                 mfl_flow top atlas X s t (chart_inv c y) IN FST c') /\
                      smooth_map_on W
                        (\z. SND c' (mfl_flow top atlas X s (fstcart z)
                                       (chart_inv c (sndcart z))))`;;

(* Smooth helper maps.                                                       *)

let MFL_SMOOTH_SNDCART = prove
 (`!W V (h:real^N->real^P).
        open W /\ open V /\ smooth_map_on V h /\
        (!z:real^(1,N)finite_sum. z IN W ==> sndcart z IN V)
        ==> smooth_map_on W (\z. h(sndcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z:real^(1,N)finite_sum. (h:real^N->real^P)(sndcart z)) = h o sndcart`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `V:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`; `\x:real^(1,N)finite_sum. x`;
                 `sndcart:real^(1,N)finite_sum->real^N`] SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; LINEAR_SNDCART; o_DEF; ETA_AX]);;

let MFL_SMOOTH_KMAP = prove
 (`!(J:real^1->bool) (V:real^N->bool) (h:real^N->real^N) t1:real^1.
        open J /\ open V /\ smooth_map_on V h
        ==> smooth_map_on (J PCROSS V)
              (\z. pastecart (fstcart z) (pastecart t1 (h(sndcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open((J:real^1->bool) PCROSS (V:real^N->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`(J:real^1->bool) PCROSS (V:real^N->bool)`;
                   `\x:real^(1,N)finite_sum. x`;
                   `fstcart:real^(1,N)finite_sum->real^1`] SMOOTH_MAP_ON_LINEAR_O) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; LINEAR_FSTCART; o_DEF; ETA_AX];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC MFL_SMOOTH_SNDCART THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_SIMP_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART]]);;

let MFL_SMOOTH_SLICE = prove
 (`!W (f:real^(1,N)finite_sum->real^P) t:real^1.
        open W /\ smooth_map_on W f
        ==> open {y | pastecart t y IN W} /\
            smooth_map_on {y | pastecart t y IN W} (\y. f(pastecart t y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open {y:real^N | pastecart (t:real^1) y IN W}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\y:real^N. (f:real^(1,N)finite_sum->real^P) (pastecart t y)) =
                f o (\y. pastecart t y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]);;

(* The base case and the passage from joint to fixed-time smoothness.       *)

let MFL_PSMOOTH_REFL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s.
        mfl_hyp top atlas X J K /\ s IN J ==> mfl_psmooth top atlas X s s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfl_psmooth] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                       `y0:real^N`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND c) (FST c)
        ==> mfl_flow top atlas (X:real->A->real^N) s s
              (chart_inv (c:(A->bool)#(A->real^N)) y) = chart_inv c y`
  (LABEL_TAC "refl") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y0 IN FST (c':(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfl_flow top atlas (X:real->A->real^N) s s
                   (chart_inv (c:(A->bool)#(A->real^N)) y0) IN
                 FST (c':(A->bool)#(A->real^N))` THEN
    USE_THEN "refl" (fun th -> SIMP_TAC[MATCH_MP th
      (ASSUME `(y0:real^N) IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`)]);
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N)))
                    (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
      CHART_OVERLAP_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC `chart_trans (c:(A->bool)#(A->real^N)) (c':(A->bool)#(A->real^N))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; chart_trans] THEN
      X_GEN_TAC `p:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
        CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]]]);;

let MFL_JSMOOTH_IMP_PSMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J s t.
        mfl_jsmooth top atlas X J s t ==> mfl_psmooth top atlas X s t`,
  REWRITE_TAC[mfl_jsmooth; mfl_psmooth] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(LABEL_TAC "js") THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                       `y0:real^N`] THEN STRIP_TAC THEN
  USE_THEN "js" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                                 `y0:real^N`]) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^(1,N)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:real^(1,N)finite_sum->bool`;
                 `\z. SND (c':(A->bool)#(A->real^N))
                        (mfl_flow top atlas (X:real->A->real^N) s (fstcart z)
                           (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))`;
                 `t:real^1`] MFL_SMOOTH_SLICE) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN STRIP_TAC THEN
  EXISTS_TAC `{y:real^N | pastecart (t:real^1) y IN W}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* One propagation step.  If the flow from s is smooth in charts at time t1, *)
(* then near any time t0 within one uniform step it is jointly smooth: in K  *)
(* it is a chart flow from time t1 composed with the map at time t1          *)
(* (ODE_FLOW_SMOOTH), off K it does not move.                                *)
(* ------------------------------------------------------------------------- *)

(* The chart flow from time t1 after a smooth map h, in a second chart.     *)

let MFL_CHART_FLOW_COMPOSE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) (J:real^1->bool) K
    c1 c' (t1:real^1) (Wh:real^N->bool) (h:real^N->real^N).
        mfl_hyp top atlas X J K /\ c1 IN atlas /\ c' IN atlas /\ t1 IN J /\
        open Wh /\ smooth_map_on Wh h /\
        (!y. y IN Wh ==> h y IN IMAGE (SND c1) (FST c1))
        ==> open {z | z IN J PCROSS Wh /\
                      pastecart (fstcart z) (pastecart t1 (h(sndcart z))) IN
                      ode_domain (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1)) /\
                      ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1))
                        (fstcart z) (pastecart t1 (h(sndcart z))) IN
                      IMAGE (SND c1) (FST c1 INTER FST c')} /\
            smooth_map_on
              {z | z IN J PCROSS Wh /\
                   pastecart (fstcart z) (pastecart t1 (h(sndcart z))) IN
                   ode_domain (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1)) /\
                   ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1))
                     (fstcart z) (pastecart t1 (h(sndcart z))) IN
                   IMAGE (SND c1) (FST c1 INTER FST c')}
              (\z. chart_trans c1 c'
                     (ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1))
                        (fstcart z) (pastecart t1 (h(sndcart z)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c1:(A->bool)#(A->real^N)`] MFL_HYP_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mfl_field atlas (X:real->A->real^N) c1`;
                 `(J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1)`]
    ODE_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `Dom = ode_domain (mfl_field atlas (X:real->A->real^N) c1)
                      ((J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1))` THEN
  ABBREV_TAC `G = \w:real^(1,(1,N)finite_sum)finite_sum.
                    ode_flow (mfl_field atlas (X:real->A->real^N) c1)
                      ((J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1))
                      (fstcart w) (sndcart w)` THEN
  ABBREV_TAC `k = \z:real^(1,N)finite_sum.
                    pastecart (fstcart z) (pastecart (t1:real^1) ((h:real^N->real^N)(sndcart z)))` THEN
  SUBGOAL_THEN `open (Dom:real^(1,(1,N)finite_sum)finite_sum->bool) /\
                smooth_map_on Dom (G:real^(1,(1,N)finite_sum)finite_sum->real^N)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dom" THEN EXPAND_TAC "G" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(1,N)finite_sum.
        ode_flow (mfl_field atlas (X:real->A->real^N) c1)
          ((J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1))
          (fstcart z) (pastecart t1 ((h:real^N->real^N)(sndcart z))) =
        (G:real^(1,(1,N)finite_sum)finite_sum->real^N) (k z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "G" THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^(1,N)finite_sum.
       pastecart (fstcart z) (pastecart t1 ((h:real^N->real^N)(sndcart z))) =
       (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) z`
  (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "k" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ((J:real^1->bool) PCROSS (Wh:real^N->bool))
       (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) /\
    open ((J:real^1->bool) PCROSS (Wh:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS] THEN EXPAND_TAC "k" THEN
    MATCH_MP_TAC MFL_SMOOTH_KMAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `W2 = {z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
              (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) z IN Dom}` THEN
  SUBGOAL_THEN `open(W2:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W2" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (W2:real^(1,N)finite_sum->bool)
      ((G:real^(1,(1,N)finite_sum)finite_sum->real^N) o
       (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `Dom:real^(1,(1,N)finite_sum)finite_sum->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "W2" THEN SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(J:real^1->bool) PCROSS (Wh:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "W2" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
         (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) z IN Dom /\
         (G:real^(1,(1,N)finite_sum)finite_sum->real^N) (k z) IN
         IMAGE (SND (c1:(A->bool)#(A->real^N)))
               (FST c1 INTER FST (c':(A->bool)#(A->real^N)))} =
    {z | z IN W2 /\ (G o k) z IN IMAGE (SND c1) (FST c1 INTER FST c')}`
  SUBST1_TAC THENL
   [EXPAND_TAC "W2" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; CONJ_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE (SND (c1:(A->bool)#(A->real^N)))
                (FST c1 INTER FST (c':(A->bool)#(A->real^N))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c1:(A->bool)#(A->real^N))`; `SND(c1:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
      CHART_OVERLAP_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[PAIR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN (W2:real^(1,N)finite_sum->bool) /\
              ((G:real^(1,(1,N)finite_sum)finite_sum->real^N) o
               (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum)) z IN
              IMAGE (SND (c1:(A->bool)#(A->real^N)))
                    (FST c1 INTER FST (c':(A->bool)#(A->real^N)))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL
     [`(G:real^(1,(1,N)finite_sum)finite_sum->real^N) o
       (k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum)`;
      `W2:real^(1,N)finite_sum->bool`;
      `IMAGE (SND (c1:(A->bool)#(A->real^N)))
             (FST c1 INTER FST (c':(A->bool)#(A->real^N)))`]
     CONTINUOUS_OPEN_PREIMAGE) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z. chart_trans (c1:(A->bool)#(A->real^N)) (c':(A->bool)#(A->real^N))
           ((G:real^(1,(1,N)finite_sum)finite_sum->real^N)
             ((k:real^(1,N)finite_sum->real^(1,(1,N)finite_sum)finite_sum) z))) =
    chart_trans c1 c' o (G o k)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (SND (c1:(A->bool)#(A->real^N)))
                    (FST c1 INTER FST (c':(A->bool)#(A->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `W2:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c1:(A->bool)#(A->real^N))`; `SND(c1:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`]
      CHART_TRANS_SMOOTH) THEN
    ASM_REWRITE_TAC[PAIR]]);;

let MFL_CHART_IMAGE_INTER = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c U y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> (y IN IMAGE (SND c) (FST c INTER U) <=> chart_inv c y IN U)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:A` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y` THEN
    ASM_SIMP_TAC[]]);;

(* The flow from s after time t1 is the chart flow from time t1.           *)

let MFL_STEP_POINT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t1 t c c1 y.
        mfl_hyp top atlas X J K /\ s IN J /\ t1 IN J /\ c IN atlas /\ c1 IN atlas /\
        y IN IMAGE (SND c) (FST c) /\
        mfl_flow top atlas X s t1 (chart_inv c y) IN FST c1 /\
        t IN ode_maxint (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1))
               (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c y))))
        ==> t IN J /\
            ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1)) t
              (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c y)))) IN
            IMAGE (SND c1) (FST c1) /\
            mfl_flow top atlas X s t (chart_inv c y) =
            chart_inv c1
              (ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1)) t
                 (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c y)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c1:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ABBREV_TAC `p = mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                    (X:real->A->real^N) s t1 (chart_inv (c:(A->bool)#(A->real^N)) y)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c1:(A->bool)#(A->real^N)`; `t1:real^1`;
                 `SND (c1:(A->bool)#(A->real^N)) p`; `t:real^1`] MFL_FLOW_CHART) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "p" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFL_FLOW_COCYCLE THEN
  MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                        `c:(A->bool)#(A->real^N)`] THEN
  ASM_SIMP_TAC[]);;

(* The step inside K: chart flow in a chart c1 from time t1.                *)

let MFL_STEP_INK = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t1 t0 c c' c1 y0.
        mfl_hyp top atlas X J K /\ s IN J /\ t1 IN J /\ t0 IN J /\
        c IN atlas /\ c' IN atlas /\ c1 IN atlas /\ y0 IN IMAGE (SND c) (FST c) /\
        mfl_flow top atlas X s t1 (chart_inv c y0) IN FST c1 /\
        mfl_flow top atlas X s t0 (chart_inv c y0) IN FST c' /\
        t0 IN ode_maxint (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1))
                (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c y0)))) /\
        mfl_psmooth top atlas X s t1
        ==> ?W. open W /\ pastecart t0 y0 IN W /\
                (!t y. pastecart t y IN W
                       ==> t IN J /\ y IN IMAGE (SND c) (FST c) /\
                           mfl_flow top atlas X s t (chart_inv c y) IN FST c') /\
                smooth_map_on W
                  (\z. SND c' (mfl_flow top atlas X s (fstcart z)
                                 (chart_inv c (sndcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c1:(A->bool)#(A->real^N)`;
                                `y0:real^N`] o GEN_REWRITE_RULE I [mfl_psmooth]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Wh:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wh") ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `c1:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                 `t1:real^1`; `Wh:real^N->bool`;
                 `\y. SND (c1:(A->bool)#(A->real^N))
                        (mfl_flow top atlas (X:real->A->real^N) s t1
                           (chart_inv (c:(A->bool)#(A->real^N)) y))`]
    MFL_CHART_FLOW_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "wh" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:real^N) IN Wh`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC
   `S = {z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
             pastecart (fstcart z)
               (pastecart (t1:real^1)
                  (SND (c1:(A->bool)#(A->real^N))
                     (mfl_flow top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N)
                        s t1 (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))))) IN
             ode_domain (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1)) /\
             ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1))
               (fstcart z)
               (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c (sndcart z))))) IN
             IMAGE (SND c1) (FST c1 INTER FST (c':(A->bool)#(A->real^N)))}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cs")) THEN
  SUBGOAL_THEN
   `!t y. pastecart t y IN S
          ==> t IN J /\ y IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))) /\
              ode_flow (mfl_field atlas (X:real->A->real^N) c1)
                ((J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1)) t
                (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c y)))) IN
              IMAGE (SND c1) (FST c1 INTER FST (c':(A->bool)#(A->real^N))) /\
              mfl_flow top atlas X s t (chart_inv c y) =
              chart_inv c1
                (ode_flow (mfl_field atlas X c1) (J PCROSS IMAGE (SND c1) (FST c1)) t
                   (pastecart t1 (SND c1 (mfl_flow top atlas X s t1 (chart_inv c y)))))`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                ODE_IN_DOMAIN] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "wh" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:real^N) IN Wh`))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `s:real^1`; `t1:real^1`; `t:real^1`; `c:(A->bool)#(A->real^N)`;
                   `c1:(A->bool)#(A->real^N)`; `y:real^N`] MFL_STEP_POINT) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                ODE_IN_DOMAIN] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `s:real^1`; `t1:real^1`; `t0:real^1`; `c:(A->bool)#(A->real^N)`;
                   `c1:(A->bool)#(A->real^N)`; `y0:real^N`] MFL_STEP_POINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c1:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[PASTECART_IN_PCROSS; FUN_IN_IMAGE] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c1:(A->bool)#(A->real^N)`; `FST(c':(A->bool)#(A->real^N))`;
                   `ode_flow (mfl_field atlas (X:real->A->real^N) c1)
                      ((J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1))
                      t0 (pastecart t1 (SND c1 (mfl_flow top atlas X s t1
                                         (chart_inv (c:(A->bool)#(A->real^N)) y0))))`]
      MFL_CHART_IMAGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `pastecart (t:real^1) (y:real^N) IN S`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c1:(A->bool)#(A->real^N)`; `FST(c':(A->bool)#(A->real^N))`;
                   `ode_flow (mfl_field atlas (X:real->A->real^N) c1)
                      ((J:real^1->bool) PCROSS IMAGE (SND (c1:(A->bool)#(A->real^N))) (FST c1))
                      t (pastecart t1 (SND c1 (mfl_flow top atlas X s t1
                                         (chart_inv (c:(A->bool)#(A->real^N)) y))))`]
      MFL_CHART_IMAGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    USE_THEN "cs" (fun th -> MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
                             EXISTS_TAC (rand(concl th))) THEN
    USE_THEN "cs" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `pastecart (t:real^1) (y:real^N) IN S`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[chart_trans]]);;

(* The step off K: there the flow does not move.                            *)

let MFL_STEP_OFFK = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t1 t0 c c' y0.
        mfl_hyp top atlas X J K /\ s IN J /\ t1 IN J /\ t0 IN J /\
        c IN atlas /\ c' IN atlas /\ y0 IN IMAGE (SND c) (FST c) /\
        ~(mfl_flow top atlas X s t1 (chart_inv c y0) IN K) /\
        mfl_flow top atlas X s t0 (chart_inv c y0) IN FST c' /\
        mfl_psmooth top atlas X s t1
        ==> ?W. open W /\ pastecart t0 y0 IN W /\
                (!t y. pastecart t y IN W
                       ==> t IN J /\ y IN IMAGE (SND c) (FST c) /\
                           mfl_flow top atlas X s t (chart_inv c y) IN FST c') /\
                smooth_map_on W
                  (\z. SND c' (mfl_flow top atlas X s (fstcart z)
                                 (chart_inv c (sndcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))
        ==> chart_inv c y IN topspace top`
  (LABEL_TAC "ctop") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_CHART_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`;
                          `c:(A->bool)#(A->real^N)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. t IN J /\ y IN IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))) /\
          ~(mfl_flow top atlas (X:real->A->real^N) s t1 (chart_inv c y) IN K)
          ==> mfl_flow top atlas X s t (chart_inv c y) =
              mfl_flow top atlas X s t1 (chart_inv c y)`
  (LABEL_TAC "fix") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `s:real^1`; `t1:real^1`; `t:real^1`;
                   `chart_inv (c:(A->bool)#(A->real^N)) y`] MFL_FLOW_COCYCLE) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFL_FLOW_OFFK THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfl_flow top atlas (X:real->A->real^N) s t1 (chart_inv (c:(A->bool)#(A->real^N)) y0)
    IN FST (c':(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [USE_THEN "fix" (fun th -> MP_TAC(SPECL [`t0:real^1`; `y0:real^N`] th)) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                                `y0:real^N`] o GEN_REWRITE_RULE I [mfl_psmooth]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Wh:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "wh") ASSUME_TAC)))) THEN
  ABBREV_TAC
   `Op = IMAGE (SND (c':(A->bool)#(A->real^N))) (FST c' INTER (topspace top DIFF K))` THEN
  SUBGOAL_THEN `open (Op:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Op" THEN MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; COMPACT_IN_IMP_CLOSED_IN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on ((J:real^1->bool) PCROSS (Wh:real^N->bool))
      (\z. SND (c':(A->bool)#(A->real^N))
             (mfl_flow top atlas (X:real->A->real^N) s t1
                (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(J:real^1->bool) PCROSS (Wh:real^N->bool)`; `Wh:real^N->bool`;
                   `\y. SND (c':(A->bool)#(A->real^N))
                          (mfl_flow top atlas (X:real->A->real^N) s t1
                             (chart_inv (c:(A->bool)#(A->real^N)) y))`]
      MFL_SMOOTH_SNDCART) THEN
    ASM_SIMP_TAC[OPEN_PCROSS; FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART];
    ALL_TAC] THEN
  EXISTS_TAC
   `{z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
         SND (c':(A->bool)#(A->real^N))
           (mfl_flow top atlas (X:real->A->real^N) s t1
              (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))) IN (Op:real^N->bool)}` THEN
  SUBGOAL_THEN
   `!t y. pastecart t y IN
          {z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
               SND (c':(A->bool)#(A->real^N))
                 (mfl_flow top atlas (X:real->A->real^N) s t1
                    (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))) IN (Op:real^N->bool)}
          ==> t IN J /\ y IN IMAGE (SND c) (FST c) /\
              mfl_flow top atlas X s t (chart_inv c y) =
              mfl_flow top atlas X s t1 (chart_inv c y) /\
              mfl_flow top atlas X s t1 (chart_inv c y) IN FST c'`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN STRIP_TAC THEN
    USE_THEN "wh" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(y:real^N) IN Wh`))) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "fix" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `SND (c':(A->bool)#(A->real^N))
        (mfl_flow top atlas (X:real->A->real^N) s t1
           (chart_inv (c:(A->bool)#(A->real^N)) y)) IN (Op:real^N->bool)` THEN
    EXPAND_TAC "Op" THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c':(A->bool)#(A->real^N)`; `topspace top DIFF (K:A->bool)`;
                   `SND (c':(A->bool)#(A->real^N))
                      (mfl_flow top atlas (X:real->A->real^N) s t1
                         (chart_inv (c:(A->bool)#(A->real^N)) y))`]
      MFL_CHART_IMAGE_INTER) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[OPEN_PCROSS; SMOOTH_MAP_ON_CONTINUOUS_ON];
    REWRITE_TAC[IN_ELIM_THM; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Op" THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; IN_DIFF] THEN
    MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME
     `pastecart (t:real^1) (y:real^N) IN
      {z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
           SND (c':(A->bool)#(A->real^N))
             (mfl_flow top atlas (X:real->A->real^N) s t1
                (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))) IN (Op:real^N->bool)}`))) THEN
    SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\z:real^(1,N)finite_sum. SND (c':(A->bool)#(A->real^N))
            (mfl_flow top atlas (X:real->A->real^N) s t1
               (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN DISCH_TAC THEN
      USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th (ASSUME
       `pastecart (t:real^1) (y:real^N) IN
        {z | z IN (J:real^1->bool) PCROSS (Wh:real^N->bool) /\
             SND (c':(A->bool)#(A->real^N))
               (mfl_flow top atlas (X:real->A->real^N) s t1
                  (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))) IN (Op:real^N->bool)}`))) THEN
      SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(J:real^1->bool) PCROSS (Wh:real^N->bool)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Propagation of smoothness along segments; joint smoothness on the open    *)
(* time-state sets of the statements; continuity, smoothness in charts and   *)
(* the diffeomorphism property of each flow map.                             *)
(* ------------------------------------------------------------------------- *)

let MFL_STEP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K Tw e s t1 t0.
        mfl_hyp top atlas X J K /\
        (!t1 t. t1 IN Tw /\ dist(t,t1) <= e ==> t IN J) /\
        (!x. x IN K
             ==> ?c. c IN atlas /\ x IN FST c /\
                     !t1 t. t1 IN Tw /\ dist(t,t1) <= e
                            ==> t IN ode_maxint (mfl_field atlas X c)
                                       (J PCROSS IMAGE (SND c) (FST c))
                                       (pastecart t1 (SND c x))) /\
        s IN J /\ t1 IN Tw /\ dist(t0,t1) <= e /\ mfl_psmooth top atlas X s t1
        ==> mfl_jsmooth top atlas X J s t0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "margin")
    (CONJUNCTS_THEN2 (LABEL_TAC "kch") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(t1:real^1) IN J /\ (t0:real^1) IN J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "margin" MATCH_MP_TAC THEN EXISTS_TAC `t1:real^1` THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_MESON_TAC[DIST_POS_LE; REAL_LE_TRANS];
    ALL_TAC] THEN
  REWRITE_TAC[mfl_jsmooth] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                       `y0:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `mfl_flow top atlas (X:real->A->real^N) s t1 (chart_inv (c:(A->bool)#(A->real^N)) y0)
    IN K` THENL
   [USE_THEN "kch" (fun th -> MP_TAC(MATCH_MP th (ASSUME
     `mfl_flow top atlas (X:real->A->real^N) s t1
        (chart_inv (c:(A->bool)#(A->real^N)) y0) IN K`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `c1:(A->bool)#(A->real^N)` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MFL_STEP_INK THEN
    MAP_EVERY EXISTS_TAC [`K:A->bool`; `t1:real^1`; `c1:(A->bool)#(A->real^N)`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC MFL_STEP_OFFK THEN
    MAP_EVERY EXISTS_TAC [`K:A->bool`; `t1:real^1`] THEN ASM_REWRITE_TAC[]]);;

let MFL_JSMOOTH_ALL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J
        ==> mfl_psmooth top atlas X s t /\ mfl_jsmooth top atlas X J s t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET J` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_MESON_TAC[mfl_hyp; IS_INTERVAL_CONVEX_1];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `segment[s:real^1,t]`] MFL_UNIFORM) THEN
  ASM_REWRITE_TAC[COMPACT_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!r. r IN segment[s,t]
                    ==> mfl_psmooth top (atlas:((A->bool)#(A->real^N))->bool)
                                    (X:real->A->real^N) s r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(BETA_RULE(ISPECL
     [`\r. mfl_psmooth top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) s r`;
      `s:real^1`; `t:real^1`; `e:real`] MFL_SEGMENT_INDUCT)) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFL_PSMOOTH_REFL THEN
      MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`r1:real^1`; `r:real^1`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MFL_JSMOOTH_IMP_PSMOOTH THEN EXISTS_TAC `J:real^1->bool` THEN
    MATCH_MP_TAC MFL_STEP THEN
    MAP_EVERY EXISTS_TAC [`K:A->bool`; `segment[s:real^1,t]`; `e:real`; `r1:real^1`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `segment[s:real^1,r] SUBSET segment[s,t]` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT];
        ASM SET_TAC[]];
      ASM_MESON_TAC[DIST_SYM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfl_psmooth top (atlas:((A->bool)#(A->real^N))->bool)
                            (X:real->A->real^N) s t`
  ASSUME_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFL_STEP THEN
  MAP_EVERY EXISTS_TAC [`K:A->bool`; `segment[s:real^1,t]`; `e:real`; `t:real^1`] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT; DIST_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* Joint smoothness on the open set of the statements.                     *)

let MFL_JOINT_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K c c' s.
        mfl_hyp top atlas X J K /\ c IN atlas /\ c' IN atlas /\ s IN J
        ==> open {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                  mfl_flow top atlas X s t (chart_inv c y) IN FST c'} /\
            smooth_map_on
              {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                               mfl_flow top atlas X s t (chart_inv c y) IN FST c'}
              (\z. SND c' (mfl_flow top atlas X s (fstcart z) (chart_inv c (sndcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                              mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                                (X:real->A->real^N) s t
                                (chart_inv (c:(A->bool)#(A->real^N)) y) IN
                              FST (c':(A->bool)#(A->real^N))}
        ==> ?W. open W /\ z IN W /\
                W SUBSET {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                          mfl_flow top atlas X s t (chart_inv c y) IN FST c'} /\
                smooth_map_on W
                  (\z. SND c' (mfl_flow top atlas X s (fstcart z)
                                 (chart_inv c (sndcart z))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
    MAP_EVERY X_GEN_TAC [`t0:real^1`; `y0:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `s:real^1`; `t0:real^1`] MFL_JSMOOTH_ALL) THEN
    ASM_REWRITE_TAC[mfl_jsmooth] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                               `y0:real^N`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `W:real^(1,N)finite_sum->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_MESON_TAC[]]);;

(* Continuity of the flow maps.                                              *)

let MFL_FLOW_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J
        ==> continuous_map (top,top) (mfl_flow top atlas X s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `s:real^1`; `t:real^1`] MFL_JSMOOTH_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ps" o CONJUNCT1) THEN
  REWRITE_TAC[continuous_map] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x0:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfl_flow top atlas (X:real->A->real^N) s t (x0:A) IN topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_IN THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c c':(A->bool)#(A->real^N).
        c IN atlas /\ (x0:A) IN FST c /\ c' IN atlas /\
        mfl_flow top atlas (X:real->A->real^N) s t x0 IN FST c'`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x0:A)`;
      `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                (mfl_flow top atlas (X:real->A->real^N) s t (x0:A))`] THEN
    ASM_MESON_TAC[CHART_AT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c':(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  USE_THEN "ps" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                                 `SND (c:(A->bool)#(A->real^N)) x0`] o
                 GEN_REWRITE_RULE I [mfl_psmooth]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "w") ASSUME_TAC)))) THEN
  ABBREV_TAC
   `G = {y | y IN W /\
             SND (c':(A->bool)#(A->real^N))
               (mfl_flow top atlas (X:real->A->real^N) s t
                  (chart_inv (c:(A->bool)#(A->real^N)) y)) IN
             IMAGE (SND c') (FST c' INTER (u:A->bool))}` THEN
  SUBGOAL_THEN `open(G:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
    MATCH_MP_TAC MFL_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{p:A | p IN FST (c:(A->bool)#(A->real^N)) /\ SND c p IN G}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFL_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:A` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MFL_CHART_IN_TOPSPACE]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (p:A)) = p` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `SND (c:(A->bool)#(A->real^N)) (p:A) IN G` THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    USE_THEN "w" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `SND (c:(A->bool)#(A->real^N)) (p:A) IN W`))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c':(A->bool)#(A->real^N)`; `u:A->bool`;
                   `SND (c':(A->bool)#(A->real^N))
                      (mfl_flow top atlas (X:real->A->real^N) s t (p:A))`]
      MFL_CHART_IMAGE_INTER) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* Smoothness in charts and the diffeomorphism property.                     *)

let MFL_FLOW_SMOOTH_MAP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J
        ==> mfd_smooth_map atlas atlas (topspace top) (mfl_flow top atlas X s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfl_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                 `s:real^1`; `t:real^1`] MFL_JSMOOTH_ALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ps" o CONJUNCT1) THEN
  REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`] THEN
  STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                   `topspace top:A->bool`;
                   `mfl_flow top atlas (X:real->A->real^N) s t`]
      MFDM_CHART_DOMAIN_OPEN) THEN
    ASM_SIMP_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC MFL_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "ps" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                                 `SND (c:(A->bool)#(A->real^N)) x`] o
                 GEN_REWRITE_RULE I [mfl_psmooth]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `W:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\y. SND (c':(A->bool)#(A->real^N))
                    (mfl_flow top atlas (X:real->A->real^N) s t
                       (chart_inv (c:(A->bool)#(A->real^N)) y))` THEN
  ASM_REWRITE_TAC[o_THM]);;

let MFL_FLOW_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) X J K s t.
        mfl_hyp top atlas X J K /\ s IN J /\ t IN J
        ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                       (mfl_flow top atlas X s t) (mfl_flow top atlas X t s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE; homeomorphic_maps] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFL_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `s:real^1`; `t:real^1`; `s:real^1`; `x:A`] MFL_FLOW_COCYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MFL_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `t:real^1`; `s:real^1`; `t:real^1`; `x:A`] MFL_FLOW_COCYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MFL_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFL_FLOW_SMOOTH_MAP THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MFL_FLOW_SMOOTH_MAP THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The general flow theorem MFLOW_GEN (open time interval J, field vanishing *)
(* off a compact K, two-parameter flow with the cocycle law) and the two     *)
(* statements SMT_REQ_MFLOW_STATEMENT (J = R, s = 0) and                     *)
(* PDE_REQ_MFLOW_STATEMENT of pc_pde_iface (J = (a,b), K = the compact       *)
(* space).                                                                   *)
(* ------------------------------------------------------------------------- *)

let MFLOW_GEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J K.
        mfl_hyp top atlas X J K
        ==> (!s x. s IN J /\ x IN topspace top ==> mfl_flow top atlas X s s x = x) /\
            (!s r t x. s IN J /\ r IN J /\ t IN J /\ x IN topspace top
                       ==> mfl_flow top atlas X r t (mfl_flow top atlas X s r x) =
                           mfl_flow top atlas X s t x) /\
            (!s t. s IN J /\ t IN J
                   ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                         (mfl_flow top atlas X s t) (mfl_flow top atlas X t s)) /\
            (!s t x. s IN J /\ t IN J /\ x IN topspace top DIFF K
                     ==> mfl_flow top atlas X s t x = x) /\
            (!c s t x. c IN atlas /\ s IN J /\ t IN J /\ x IN topspace top /\
                       mfl_flow top atlas X s t x IN FST c
                       ==> ((\r. SND c (mfl_flow top atlas X s r x)) has_vector_derivative
                            mfd_vrep atlas (X (drop t)) c
                              (SND c (mfl_flow top atlas X s t x))) (at t)) /\
            (!c c' s. c IN atlas /\ c' IN atlas /\ s IN J
                      ==> smooth_map_on
                            {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                             mfl_flow top atlas X s t (chart_inv c y) IN
                                             FST c'}
                            (\z. SND c' (mfl_flow top atlas X s (fstcart z)
                                           (chart_inv c (sndcart z)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_COCYCLE THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_OFFK THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MFL_FLOW_DERIV THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `K:A->bool`;
                   `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`; `s:real^1`]
      MFL_JOINT_SMOOTH) THEN
    ASM_SIMP_TAC[]]);;

(* SMT_REQ_MFLOW_STATEMENT (Lee, Theorem 9.16 and Theorem 9.48).            *)

let SMT_REQ_MFLOW = prove
 (`!(u:A->bool) (n:N->bool). SMT_REQ_MFLOW_STATEMENT u n`,
  REWRITE_TAC[SMT_REQ_MFLOW_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `(:real^1)`; `K:A->bool`] MFLOW_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfl_hyp; mfl_field; OPEN_UNIV; IS_INTERVAL_UNIV] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "refl") (CONJUNCTS_THEN2 (LABEL_TAC "coc")
   (CONJUNCTS_THEN2 (LABEL_TAC "dif") (CONJUNCTS_THEN2 (LABEL_TAC "offk")
   (CONJUNCTS_THEN2 (LABEL_TAC "der") (LABEL_TAC "js")))))) THEN
  EXISTS_TAC `\t. mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                    (X:real->A->real^N) (vec 0) (lift t)` THEN
  REWRITE_TAC[LIFT_NUM; LIFT_DROP] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "refl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN
    EXISTS_TAC `mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                  (X:real->A->real^N) (lift t) (vec 0)` THEN
    USE_THEN "dif" (fun th -> REWRITE_TAC[th]);
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN DISCH_TAC THEN
    USE_THEN "offk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real`; `x:A`] THEN STRIP_TAC THEN
    USE_THEN "der" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `vec 0:real^1`;
                                    `lift t`; `x:A`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[LIFT_DROP];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`] THEN
    STRIP_TAC THEN
    USE_THEN "js" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                                   `vec 0:real^1`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(1,N)finite_sum` THEN
    EQ_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`drop t`; `y:real^N`] THEN ASM_REWRITE_TAC[LIFT_DROP];
      MAP_EVERY EXISTS_TAC [`lift t`; `y:real^N`] THEN ASM_REWRITE_TAC[]]]);;

(* PDE_REQ_MFLOW_STATEMENT of pc_pde_iface.                                 *)

let PDE_REQ_MFLOW = prove
 (`!(u:A->bool) (n:N->bool). PDE_REQ_MFLOW_STATEMENT u n`,
  REWRITE_TAC[PDE_REQ_MFLOW_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `interval(lift a,lift b)`; `topspace top:A->bool`]
    MFLOW_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[mfl_hyp; mfl_field; OPEN_INTERVAL; IS_INTERVAL_INTERVAL; DIFF_EQ_EMPTY;
                    NOT_IN_EMPTY; GSYM compact_space] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "refl") (CONJUNCTS_THEN2 (LABEL_TAC "coc")
   (CONJUNCTS_THEN2 (LABEL_TAC "dif") (CONJUNCTS_THEN2 (LABEL_TAC "offk")
   (CONJUNCTS_THEN2 (LABEL_TAC "der") (LABEL_TAC "js")))))) THEN
  SUBGOAL_THEN `!r. lift r IN interval(lift a,lift b) <=> a < r /\ r < b`
  (LABEL_TAC "inj") THENL [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  EXISTS_TAC `\t. mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                    (X:real->A->real^N) (lift s) (lift t)` THEN
  REWRITE_TAC[LIFT_DROP] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN USE_THEN "refl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    EXISTS_TAC `mfl_flow top (atlas:((A->bool)#(A->real^N))->bool)
                  (X:real->A->real^N) (lift t) (lift s)` THEN
    USE_THEN "dif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real`; `x:A`] THEN STRIP_TAC THEN
    USE_THEN "der" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `lift s`;
                                    `lift t`; `x:A`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[LIFT_DROP];
    MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`] THEN
    STRIP_TAC THEN
    USE_THEN "js" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                                   `lift s`]) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(1,N)finite_sum` THEN
    EQ_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`drop t`; `y:real^N`] THEN
      UNDISCH_TAC `(t:real^1) IN interval(lift a,lift b)` THEN
      ASM_REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1];
      MAP_EVERY EXISTS_TAC [`lift t`; `y:real^N`] THEN ASM_REWRITE_TAC[]]]);;

