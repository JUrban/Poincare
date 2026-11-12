(* ========================================================================= *)
(* Flows of time-dependent smooth vector fields on Hausdorff manifolds       *)
(* WITHOUT compact support, under an escape function: a smooth function Fe   *)
(* with compact sets abs Fe <= c whose derivative along X t is at most       *)
(* C (1 + abs Fe) on compact time intervals (mcf_escape).                    *)
(* Then mfl_flow (pc_mfd_flow) of X has the conclusions of MFLOW_GEN:        *)
(* identity, cocycle law, diffeomorphisms, the time derivative in charts     *)
(* and joint smoothness in charts (MCF_FLOW_GEN).                            *)
(* Route: along any integral curve, 1 + F^2 grows at most exponentially      *)
(* (ODE_GRONWALL_DERIV), so on a time window the curves from abs F <= M stay *)
(* in abs F <= M'; a smooth cut-off chi = 1 there (MFD_SMOOTH_CUTOFF) gives  *)
(* the compactly supported field chi X, whose flow (MFLOW_GEN) agrees with   *)
(* that of X on the window; every property is local in time and space.       *)
(* MCF_LOCAL_AGREE states this local agreement: near each point, on a time   *)
(* window, the flow of X is the flow of a cut-off field satisfying mfl_hyp,  *)
(* so every mfl_hyp lemma applies there.                                     *)
(* pc_mfd_embed is needed for GRGE_MFD_SMOOTH_CONTINUOUS (continuity of Fe)  *)
(* and brings pc_mfd_diff (MFDD_SMOOTH_MAP_LOCAL, MFDD_SMOOTH_MAP_EQ).       *)
(* Used for the soliton flow of MT Prop 9.46 (pc_p2b_p946).                  *)
(* ========================================================================= *)

needs "src/pc_mfd_flow.ml";;
needs "src/pc_mfd_cutoff.ml";;
needs "src/pc_mfd_embed.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Escape functions, the hypothesis mcf_hyp, and cut-off fields chi x % X t  *)
(* x (chart representatives and smoothness).                                 *)
(* ========================================================================= *)

(* Fe is smooth, the sets abs Fe <= c are compact, and on every compact    *)
(* time interval in J the derivative of Fe along X t is at most            *)
(* C (1 + abs Fe).                                                           *)

let mcf_escape = new_definition
 `mcf_escape (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
             (X:real->A->real^N) (J:real^1->bool) (Fe:A->real) <=>
    mfd_smooth atlas (\x. lift(Fe x)) /\
    (!c. compact_in top {x | x IN topspace top /\ abs(Fe x) <= c}) /\
    (!a b. interval[a,b] SUBSET J
           ==> ?C. &0 <= C /\
                   !t x. t IN interval[a,b] /\ x IN topspace top
                         ==> abs(drop(frechet_derivative
                                   (\y. lift(Fe(chart_inv (chart_at atlas x) y)))
                                   (at (SND(chart_at atlas x) x))
                                   (X (drop t) x))) <= C * (&1 + abs(Fe x)))`;;

let mcf_hyp = new_definition
 `mcf_hyp (top:A topology) (atlas:((A->bool)#(A->real^N))->bool)
          (X:real->A->real^N) (J:real^1->bool) (Fe:A->real) <=>
    hausdorff_space top /\ smooth_manifold_atlas top atlas /\ open J /\ is_interval J /\
    (!c. c IN atlas
         ==> smooth_map_on (J PCROSS IMAGE (SND c) (FST c)) (mfl_field atlas X c)) /\
    mcf_escape top atlas X J Fe`;;

(* Chart facts at a point of a chart image, and the representative of a     *)
(* field in the preferred chart at x (as P2BX0_VREP_AT of pc_p2b_x0).        *)

let MCF_CHART_FACTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> chart_inv c y IN FST c /\ chart_inv c y IN topspace top /\
            SND c (chart_inv c y) = y /\
            chart_at atlas (chart_inv c y) IN atlas /\
            chart_inv c y IN FST(chart_at atlas (chart_inv c y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN FST c /\ SND c (chart_inv c y) = y`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CHART_AT THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

let MCF_VREP_AT = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:A->real^N) x.
     smooth_manifold_atlas top atlas /\ x IN topspace top
     ==> mfd_vrep atlas Z (chart_at atlas x) (SND(chart_at atlas x) x) = Z x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_vrep] THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`; `x:A`]
                CHART_JAC_SELF) THEN
  ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* Chart representatives are linear in the field. *)

let MCF_VREP_CMUL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (chi:A->real) (Z:A->real^N) c y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ y IN IMAGE (SND c) (FST c)
        ==> mfd_vrep atlas (\x. chi x % Z x) c y = chi(chart_inv c y) % mfd_vrep atlas Z c y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y:real^N`] MCF_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at atlas (chart_inv (c:(A->bool)#(A->real^N)) y)
                    :(A->bool)#(A->real^N)`;
                 `c:(A->bool)#(A->real^N)`; `chart_inv (c:(A->bool)#(A->real^N)) y`]
                MFL_CHART_TRANS_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_vrep] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]));;

(* The cut-off field is smooth in every chart. *)

let MCF_CUTOFF_FIELD_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) (chi:A->real) J c.
        smooth_manifold_atlas top atlas /\ open J /\ c IN atlas /\
        mfd_smooth atlas (\x. lift(chi x)) /\
        smooth_map_on (J PCROSS IMAGE (SND c) (FST c)) (mfl_field atlas X c)
        ==> smooth_map_on (J PCROSS IMAGE (SND c) (FST c))
                          (mfl_field atlas (\t x. chi x % X t x) c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDM_CHART]; ALL_TAC] THEN
  SUBGOAL_THEN `open((J:real^1->bool) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                drop(((\x:A. lift(chi x)) o chart_inv (c:(A->bool)#(A->real^N))) (sndcart z)) %
                mfl_field atlas (X:real->A->real^N) c z` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[MFL_FIELD_PASTECART; o_THM; LIFT_DROP] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MCF_VREP_CMUL THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MFL_SMOOTH_SNDCART THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(chi x))` THEN
      REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
      SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The escape function along integral curves.  Fe o gamma has derivative     *)
(* dF(X t) in the preferred chart, and 1 + F^2 grows at most exponentially   *)
(* along the curve.                                                          *)
(* ========================================================================= *)

(* The chain rule for a curve within a set followed by a differentiable map. *)

let MCF_VDERIV_CHAIN_WITHIN = prove
 (`!(f:real^1->real^M) (g:real^M->real^P) f' x s.
        (f has_vector_derivative f') (at x within s) /\ g differentiable (at (f x))
        ==> ((g o f) has_vector_derivative frechet_derivative g (at (f x)) f')
            (at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
  UNDISCH_TAC `(g:real^M->real^P) differentiable (at (f(x:real^1)))` THEN
  REWRITE_TAC[FRECHET_DERIVATIVE_WORKS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^M`; `g:real^M->real^P`; `\s:real^1. drop s % (f':real^M)`;
                 `frechet_derivative (g:real^M->real^P) (at (f(x:real^1)))`;
                 `x:real^1`; `s:real^1->bool`] DIFF_CHAIN_WITHIN) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_AT_WITHIN] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN
  ASM_SIMP_TAC[LINEAR_CMUL]);;

let MCF_CURVE_FDERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) L gamma (Fe:A->real) t.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(Fe x)) /\
        mfl_curve top atlas X L gamma /\ t IN L
        ==> ((\r. lift(Fe(gamma r))) has_vector_derivative
             frechet_derivative (\y. lift(Fe(chart_inv (chart_at atlas (gamma t)) y)))
               (at (SND(chart_at atlas (gamma t)) (gamma t)))
               (X (drop t) (gamma t))) (at t within L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real^1->A) t IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFL_CURVE_IN]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real^1->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real^1->A) t)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `((\r. SND(c:(A->bool)#(A->real^N)) ((gamma:real^1->A) r)) has_vector_derivative
     (X:real->A->real^N) (drop t) (gamma t)) (at t within L)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfl_curve top atlas (X:real->A->real^N) L (gamma:real^1->A)` THEN
    REWRITE_TAC[mfl_curve] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `t:real^1`] o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `mfd_vrep atlas ((X:real->A->real^N) (drop t)) c
                    (SND(c:(A->bool)#(A->real^N)) ((gamma:real^1->A) t)) = X (drop t) (gamma t)`
    (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "c" THEN MATCH_MP_TAC MCF_VREP_AT THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y. lift((Fe:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) differentiable
    at (SND c ((gamma:real^1->A) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(Fe x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
  EXISTS_TAC `(\y. lift((Fe:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))) o
              (\r. SND c ((gamma:real^1->A) r))` THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ !r. r IN L /\ dist(r,t) < d ==> (gamma:real^1->A) r IN FST(c:(A->bool)#(A->real^N))`
  (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean L)
                    {r | r IN L /\ (gamma:real^1->A) r IN FST(c:(A->bool)#(A->real^N))}`
    MP_TAC THENL
     [MP_TAC(ISPECL [`gamma:real^1->A`; `subtopology euclidean (L:real^1->bool)`;
                     `top:A topology`; `FST(c:(A->bool)#(A->real^N))`]
                    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[mfl_curve]; ASM_MESON_TAC[MFDM_CHART]];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^1` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_ELIM_THM] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^1` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MCF_VDERIV_CHAIN_WITHIN THEN ASM_REWRITE_TAC[]]);;

(* Gronwall along curves: 1 + F^2 grows at most like exp(3 C |t - t0|). *)

let MCF_CURVE_BOUND = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) L gamma (Fe:A->real) C t0.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(Fe x)) /\
        mfl_curve top atlas X L gamma /\ t0 IN L /\ &0 <= C /\
        (!t. t IN L
             ==> abs(drop(frechet_derivative
                       (\y. lift(Fe(chart_inv (chart_at atlas (gamma t)) y)))
                       (at (SND(chart_at atlas (gamma t)) (gamma t)))
                       (X (drop t) (gamma t)))) <= C * (&1 + abs(Fe(gamma t))))
        ==> !t. t IN L
                ==> &1 + Fe(gamma t) pow 2 <=
                    (&1 + Fe(gamma t0) pow 2) * exp(&3 * C * abs(drop t - drop t0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))))) THEN
  ABBREV_TAC
   `D = \t:real^1. frechet_derivative
          (\y. lift((Fe:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                              ((gamma:real^1->A) t)) y)))
          (at (SND(chart_at atlas (gamma t)) (gamma t)))
          ((X:real->A->real^N) (drop t) (gamma t))` THEN
  SUBGOAL_THEN
   `!t. t IN L
        ==> ((\r. lift((Fe:A->real)((gamma:real^1->A) r))) has_vector_derivative
             (D:real^1->real^1) t) (at t within L)`
  (LABEL_TAC "fd") THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN EXPAND_TAC "D" THEN
    MATCH_MP_TAC MCF_CURVE_FDERIV THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\t:real^1. &1 + (Fe:A->real)((gamma:real^1->A) t) pow 2`;
                 `\t:real^1. &2 * (Fe:A->real)((gamma:real^1->A) t) * drop((D:real^1->real^1) t)`;
                 `&3 * C`; `L:real^1->bool`; `t0:real^1`] ODE_GRONWALL_DERIV) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[mfl_curve]; ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "fd" (MP_TAC o C MATCH_MP (ASSUME `(t:real^1) IN L`)) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\x y:real^1. lift(drop x * drop y)`;
                     `\r. lift((Fe:A->real)((gamma:real^1->A) r))`;
                     `\r. lift((Fe:A->real)((gamma:real^1->A) r))`;
                     `(D:real^1->real^1) t`; `(D:real^1->real^1) t`; `t:real^1`;
                     `L:real^1->bool`] HAS_VECTOR_DERIVATIVE_BILINEAR_WITHIN) THEN
      ASM_REWRITE_TAC[BILINEAR_LIFT_MUL; LIFT_DROP] THEN
      DISCH_THEN(MP_TAC o CONJ (ISPECL [`lift(&1)`; `at (t:real^1) within L`]
                                       HAS_VECTOR_DERIVATIVE_CONST)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_ADD) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[LIFT_ADD; REAL_POW_2];
        REWRITE_TAC[VECTOR_ADD_LID; GSYM LIFT_ADD; LIFT_EQ] THEN CONV_TAC REAL_RING];
      ALL_TAC] THEN
    REMOVE_THEN "fd" (K ALL_TAC) THEN
    USE_THEN "bd" (MP_TAC o C MATCH_MP (ASSUME `(t:real^1) IN L`)) THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[] THEN
    ABBREV_TAC `u = (Fe:A->real)((gamma:real^1->A) t)` THEN
    ABBREV_TAC `v = drop(frechet_derivative
          (\y. lift((Fe:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                              ((gamma:real^1->A) t)) y)))
          (at (SND(chart_at atlas (gamma t)) (gamma t)))
          ((X:real->A->real^N) (drop t) (gamma t)))` THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * abs u * (C * (&1 + abs u))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      SUBGOAL_THEN `&0 <= C * ((abs u - &1) pow 2 + &2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &2`) THEN
        REWRITE_TAC[REAL_LE_POW_2];
        REWRITE_TAC[REAL_ARITH `(x - &1) pow 2 = x pow 2 - &2 * x + &1`] THEN
        REAL_ARITH_TAC]];
    REWRITE_TAC[REAL_MUL_ASSOC]]);;

(* ========================================================================= *)
(* Cut-off agreement.  On a compact time window, curves of X or of chi X     *)
(* from abs Fe <= M stay in abs Fe <= M' (MCF_CURVE_BOUND); with chi = 1     *)
(* there the two flows agree from abs Fe <= M (MCF_FLOW_AGREE).              *)
(* ========================================================================= *)

(* Curves inside chi = 1 are curves of chi X exactly when they are curves  *)
(* of X.                                                                     *)

let MCF_CURVE_CUTOFF = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) (chi:A->real) L gamma.
        smooth_manifold_atlas top atlas /\ (!t. t IN L ==> chi(gamma t) = &1)
        ==> (mfl_curve top atlas (\t x. chi x % X t x) L gamma <=>
             mfl_curve top atlas X L gamma)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!c t. c IN atlas /\ t IN L /\ (gamma:real^1->A) t IN FST c
          ==> mfd_vrep atlas (\x. (chi:A->real) x % (X:real->A->real^N) (drop t) x) c
                (SND c (gamma t)) =
              mfd_vrep atlas (X (drop t)) c (SND c (gamma t))`
  (LABEL_TAC "eqv") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `chi:A->real`;
                   `(X:real->A->real^N) (drop t)`; `c:(A->bool)#(A->real^N)`;
                   `SND(c:(A->bool)#(A->real^N)) ((gamma:real^1->A) t)`] MCF_VREP_CMUL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[mfl_curve] THEN EQ_TAC THEN
  (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))) THEN
   ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`c:(A->bool)#(A->real^N)`; `t:real^1`] THEN
   STRIP_TAC THEN USE_THEN "d" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `t:real^1`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   USE_THEN "eqv" (MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `t:real^1`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]));;

(* The derivative of Fe in the preferred chart is linear. *)

let MCF_DIRDERIV_CMUL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Fe:A->real) x c v.
        smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(Fe x)) /\
        x IN topspace top
        ==> frechet_derivative (\y. lift(Fe(chart_inv (chart_at atlas x) y)))
              (at (SND(chart_at atlas x) x)) (c % v) =
            c % frechet_derivative (\y. lift(Fe(chart_inv (chart_at atlas x) y)))
                  (at (SND(chart_at atlas x) x)) v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `ch = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\y. lift((Fe:A->real)(chart_inv (ch:(A->bool)#(A->real^N)) y))) differentiable
    at (SND ch (x:A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(ch:(A->bool)#(A->real^N))) (FST ch)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MFDM_CHART];
      UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(Fe x))` THEN
      REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL
    (MATCH_MP LINEAR_FRECHET_DERIVATIVE th)]));;

(* Curves on a time window [a,b] of any field with the escape bound stay in *)
(* Fe^2 <= (1 + M^2) exp(3 C (b - a)) when they start in abs Fe <= M.        *)

let MCF_CONFINE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (Z:real->A->real^N) L gamma (Fe:A->real)
    C a b M s.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(Fe x)) /\ &0 <= C /\
     mfl_curve top atlas Z L gamma /\ L SUBSET interval[a,b] /\ s IN L /\
     abs(Fe(gamma s)) <= M /\
     (!t x. t IN interval[a,b] /\ x IN topspace top
            ==> abs(drop(frechet_derivative
                      (\y. lift(Fe(chart_inv (chart_at atlas x) y)))
                      (at (SND(chart_at atlas x) x)) (Z (drop t) x))) <= C * (&1 + abs(Fe x)))
     ==> !r. r IN L
             ==> Fe(gamma r) pow 2 <= (&1 + M pow 2) * exp(&3 * C * abs(drop b - drop a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `Z:real->A->real^N`; `L:real^1->bool`; `gamma:real^1->A`;
                 `Fe:A->real`; `C:real`; `s:real^1`] MCF_CURVE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MFL_CURVE_IN; SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real^1`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r:real^1) IN interval[a,b] /\ (s:real^1) IN interval[a,b]` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `exp(&3 * C * abs(drop r - drop s)) <= exp(&3 * C * abs(drop b - drop a))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fe:A->real)((gamma:real^1->A) s) pow 2 <= M pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS;
      REAL_ARITH `abs x <= M ==> abs x <= abs M`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&1 + x <= y ==> x <= y`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + (Fe:A->real)((gamma:real^1->A) s) pow 2) *
              exp(&3 * C * abs(drop r - drop s))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2; REAL_ARITH `&0 <= x ==> &0 <= &1 + x`] THEN
  ASM_REAL_ARITH_TAC);;

(* On a time window, the flows of X and of a cut-off chi X agree from      *)
(* abs Fe <= M; their curves stay in abs Fe <= M', where chi = 1.           *)

let MCF_FLOW_AGREE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) a b M.
        mcf_hyp top atlas X J Fe /\ interval[a,b] SUBSET J
        ==> ?chi K M'.
              M <= M' /\ mfl_hyp top atlas (\t x. chi x % X t x) J K /\
              (!x. x IN topspace top /\ abs(Fe x) <= M' ==> chi x = &1) /\
              (!s t x. s IN interval[a,b] /\ t IN interval[a,b] /\ x IN topspace top /\
                       abs(Fe x) <= M
                       ==> mfl_flow top atlas X s t x =
                           mfl_flow top atlas (\t x. chi x % X t x) s t x /\
                           abs(Fe(mfl_flow top atlas X s t x)) <= M' /\
                           (?gamma. mfl_curve top atlas X (segment[s,t]) gamma /\
                                    gamma s = x /\ gamma t = mfl_flow top atlas X s t x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hyp") ASSUME_TAC) THEN
  USE_THEN "hyp" (STRIP_ASSUME_TAC o REWRITE_RULE[mcf_hyp; mcf_escape]) THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `interval[a:real^1,b] SUBSET J`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cb"))) THEN
  ABBREV_TAC `B = (&1 + M pow 2) * exp(&3 * C * abs(drop b - drop a))` THEN
  ABBREV_TAC `M' = max (abs M) (sqrt B)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `{x:A | x IN topspace top /\ abs((Fe:A->real) x) <= M'}`; `topspace top:A->bool`]
                MFD_SMOOTH_CUTOFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `V:A->bool` (X_CHOOSE_THEN `K:A->bool`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!x:A. x IN topspace top /\ abs((Fe:A->real) x) <= M' ==> chi x = &1`
  (LABEL_TAC "one") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `{x:A | x IN topspace top /\ abs((Fe:A->real) x) <= M'} SUBSET V` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfl_hyp top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x) J K`
  (LABEL_TAC "chyp") THENL
   [ASM_REWRITE_TAC[mfl_hyp] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MCF_CUTOFF_FIELD_SMOOTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(chi:A->real) x = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  (* the bound along curves of X and of chi X on the window *)
  SUBGOAL_THEN
   `!t x. t IN interval[a,b] /\ x IN topspace top
          ==> abs(drop(frechet_derivative
                    (\y. lift((Fe:A->real)(chart_inv (chart_at atlas x) y)))
                    (at (SND(chart_at atlas x) x))
                    ((chi:A->real) x % (X:real->A->real^N) (drop t) x))) <=
              C * (&1 + abs(Fe x))`
  (LABEL_TAC "Cc") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `Fe:A->real`;
                   `x:A`; `(chi:A->real) x`; `(X:real->A->real^N) (drop t) x`]
                  MCF_DIRDERIV_CMUL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DROP_CMUL; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(drop(frechet_derivative
                   (\y. lift((Fe:A->real)(chart_inv (chart_at atlas x) y)))
                   (at (SND(chart_at atlas x) x)) ((X:real->A->real^N) (drop t) x)))` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_MESON_TAC[REAL_ARITH `&0 <= x /\ x <= &1 ==> abs x <= &1`];
      USE_THEN "Cb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y pow 2 <= B ==> abs y <= M'` (LABEL_TAC "sq") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "M'" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[REAL_POW2_ABS];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`chi:A->real`; `K:A->bool`; `M':real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "M'" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET interval[a,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^1) IN J /\ (t:real^1) IN J` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `J:real^1->bool`;
                 `K:A->bool`; `s:real^1`; `t:real^1`; `x:A`] MFL_FLOW_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^1->A` (CONJUNCTS_THEN2 (LABEL_TAC "g0c")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g0f")))) THEN
  (* any curve of X or of chi X from x on the segment stays in abs Fe <= M' *)
  SUBGOAL_THEN
   `!Z g. (Z = (X:real->A->real^N) \/ Z = (\t x. (chi:A->real) x % X t x)) /\
          mfl_curve top atlas Z (segment[s,t]) g /\ g s = x
          ==> !r. r IN segment[s,t] ==> abs((Fe:A->real)(g r)) <= M'`
  (LABEL_TAC "stay") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      try lhs(concl th) = `Z:real->A->real^N` with Failure _ -> false)) THEN
    X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN USE_THEN "sq" MATCH_MP_TAC THEN
    EXPAND_TAC "B" THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `X:real->A->real^N`; `segment[s:real^1,t]`; `g:real^1->A`; `Fe:A->real`;
                     `C:real`; `a:real^1`; `b:real^1`; `M:real`; `s:real^1`] MCF_CONFINE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `segment[s:real^1,t]`;
                     `g:real^1->A`; `Fe:A->real`;
                     `C:real`; `a:real^1`; `b:real^1`; `M:real`; `s:real^1`] MCF_CONFINE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* such curves are curves of both fields *)
  SUBGOAL_THEN
   `!g. (mfl_curve top atlas (X:real->A->real^N) (segment[s,t]) g \/
         mfl_curve top atlas (\t x. (chi:A->real) x % X t x) (segment[s,t]) g) /\ g s = x
        ==> mfl_curve top atlas X (segment[s,t]) g /\
            mfl_curve top atlas (\t x. chi x % X t x) (segment[s,t]) g`
  (LABEL_TAC "both") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    (SUBGOAL_THEN `!r. r IN segment[s,t] ==> (chi:A->real)((g:real^1->A) r) = &1` ASSUME_TAC THENL
      [X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN USE_THEN "one" MATCH_MP_TAC THEN
       CONJ_TAC THENL [ASM_MESON_TAC[MFL_CURVE_IN]; ALL_TAC] THEN
       USE_THEN "stay" (MP_TAC o SPECL
         [`X:real->A->real^N`; `g:real^1->A`]) THEN
       USE_THEN "stay" (MP_TAC o SPECL
         [`\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `g:real^1->A`]) THEN
       ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
       ALL_TAC] THEN
     MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                    `X:real->A->real^N`; `chi:A->real`; `segment[s:real^1,t]`; `g:real^1->A`]
                   MCF_CURVE_CUTOFF) THEN
     ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);
    ALL_TAC] THEN
  SUBGOAL_THEN `mfl_curve top atlas (X:real->A->real^N) (segment[s,t]) g0` ASSUME_TAC THENL
   [USE_THEN "both" (MP_TAC o SPEC `g0:real^1->A`) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfl_flow top atlas (X:real->A->real^N) s t x = (g0:real^1->A) t` ASSUME_TAC THENL
   [REWRITE_TAC[mfl_flow] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:A` THEN
    REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `g1:real^1->A` STRIP_ASSUME_TAC) THEN
      USE_THEN "both" (MP_TAC o SPEC `g1:real^1->A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `J:real^1->bool`;
                     `K:A->bool`; `segment[s:real^1,t]`; `g1:real^1->A`; `g0:real^1->A`;
                     `s:real^1`] MFL_CURVE_UNIQUE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM SET_TAC[];
        DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        ASM_MESON_TAC[]];
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `g0:real^1->A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "stay" (MP_TAC o SPECL
      [`\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `g0:real^1->A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    EXISTS_TAC `g0:real^1->A` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The flow of X (MCF_FLOW_GEN).  Every property is local in time and space, *)
(* so it follows from the cut-off flows of MCF_FLOW_AGREE.                   *)
(* ========================================================================= *)

(* A compact window around finitely many times of an interval. *)

let MCF_WINDOW = prove
 (`!J (r:real^1) s t.
        is_interval J /\ r IN J /\ s IN J /\ t IN J
        ==> interval[lift(min (drop r) (min (drop s) (drop t))),
                     lift(max (drop r) (max (drop s) (drop t)))] SUBSET J /\
            r IN interval[lift(min (drop r) (min (drop s) (drop t))),
                          lift(max (drop r) (max (drop s) (drop t)))] /\
            s IN interval[lift(min (drop r) (min (drop s) (drop t))),
                          lift(max (drop r) (max (drop s) (drop t)))] /\
            t IN interval[lift(min (drop r) (min (drop s) (drop t))),
                          lift(max (drop r) (max (drop s) (drop t)))]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IS_INTERVAL_1] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?u v:real^1. u IN J /\ v IN J /\ drop u <= drop x /\ drop x <= drop v`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN `?u:real^1. u IN J /\ drop u = min (drop r) (min (drop s) (drop t))`
    (X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[REAL_ARITH `min a (min b c) = a \/ min a (min b c) = b \/
                                min a (min b c) = c`];
      ALL_TAC] THEN
    SUBGOAL_THEN `?v:real^1. v IN J /\ drop v = max (drop r) (max (drop s) (drop t))`
    (X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[REAL_ARITH `max a (max b c) = a \/ max a (max b c) = b \/
                                max a (max b c) = c`];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`u:real^1`; `v:real^1`] THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

(* Integral curves of X from every point, on every segment of J. *)

let MCF_FLOW_CURVE_EXISTS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) s t x.
        mcf_hyp top atlas X J Fe /\ s IN J /\ t IN J /\ x IN topspace top
        ==> mfl_flow top atlas X s t x IN topspace top /\
            ?gamma. mfl_curve top atlas X (segment[s,t]) gamma /\ gamma s = x /\
                    gamma t = mfl_flow top atlas X s t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real^1->bool`; `s:real^1`; `s:real^1`; `t:real^1`] MCF_WINDOW) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mcf_hyp]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `lift(min (drop s) (min (drop s) (drop t)))`;
                 `lift(max (drop s) (max (drop s) (drop t)))`;
                 `abs((Fe:A->real) x)`] MCF_FLOW_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool` (X_CHOOSE_THEN `M':real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPECL [`s:real^1`; `t:real^1`; `x:A`]))))))) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `gamma:real^1->A` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFL_CURVE_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                          `segment[s:real^1,t]`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    EXISTS_TAC `gamma:real^1->A` THEN ASM_REWRITE_TAC[]]);;

let MCF_FLOW_REFL = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) s x.
        mcf_hyp top atlas X J Fe /\ s IN J /\ x IN topspace top
        ==> mfl_flow top atlas X s s x = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `s:real^1`; `s:real^1`; `x:A`] MCF_FLOW_CURVE_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The cocycle law. *)

let MCF_FLOW_COCYCLE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) s r t x.
        mcf_hyp top atlas X J Fe /\ s IN J /\ r IN J /\ t IN J /\ x IN topspace top
        ==> mfl_flow top atlas X r t (mfl_flow top atlas X s r x) =
            mfl_flow top atlas X s t x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `is_interval(J:real^1->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `mcf_hyp top atlas (X:real->A->real^N) J (Fe:A->real)` THEN
    SIMP_TAC[mcf_hyp];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^1->bool`; `s:real^1`; `r:real^1`; `t:real^1`] MCF_WINDOW) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `a = lift(min (drop s) (min (drop r) (drop t)))` THEN
  ABBREV_TAC `b = lift(max (drop s) (max (drop r) (drop t)))` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `a:real^1`; `b:real^1`; `abs((Fe:A->real) x)`] MCF_FLOW_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi0:A->real` (X_CHOOSE_THEN `K0:A->bool`
    (X_CHOOSE_THEN `M0:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "ag0"))))))) THEN
  USE_THEN "ag0" (MP_TAC o SPECL [`s:real^1`; `r:real^1`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:real^1->A` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `mfl_flow top atlas (X:real->A->real^N) s r x IN topspace top` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFL_CURVE_IN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                          `segment[s:real^1,r]`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `a:real^1`; `b:real^1`; `M0:real`] MCF_FLOW_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `M1:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ag"))))))) THEN
  USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `r:real^1`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `t:real^1`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `mfl_flow top atlas (X:real->A->real^N) r t
      (mfl_flow top atlas (\t x. (chi:A->real) x % X t x) s r x) =
    mfl_flow top atlas (\t x. chi x % X t x) r t
      (mfl_flow top atlas (\t x. chi x % X t x) s r x)`
  SUBST1_TAC THENL
   [USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `r:real^1`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1)] THEN
    USE_THEN "ag" (MP_TAC o SPECL [`r:real^1`; `t:real^1`;
                                   `mfl_flow top atlas (X:real->A->real^N) s r x`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `J:real^1->bool`;
                 `K:A->bool`] MFLOW_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Continuity of the escape function and openness of its sublevel sets. *)

let MCF_FE_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real).
        mcf_hyp top atlas X J Fe ==> continuous_map (top,euclideanreal) Fe`,
  REWRITE_TAC[mcf_hyp; mcf_escape] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\x. lift((Fe:A->real) x)`] GRGE_MFD_SMOOTH_CONTINUOUS) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_EQ_DROP; o_DEF; LIFT_DROP; ETA_AX]);;

let MCF_SUBLEVEL_OPEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) M.
        mcf_hyp top atlas X J Fe
        ==> open_in top {x | x IN topspace top /\ abs(Fe x) < M}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. abs((Fe:A->real) x)`; `top:A topology`; `euclideanreal`;
                 `{r:real | r < M}`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_ABS THEN
  MATCH_MP_TAC MCF_FE_CONTINUOUS THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                        `J:real^1->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* A map that agrees near every point with a continuous map is continuous. *)

let MCF_CONTINUOUS_MAP_LOCAL = prove
 (`!(top:A topology) (top':B topology) f.
        (!x. x IN topspace top
             ==> ?U g. open_in top U /\ x IN U /\ continuous_map (top,top') g /\
                       (!y. y IN U ==> f y = g y))
        ==> continuous_map (top,top') f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->A->bool`; `g:A->A->B`] THEN DISCH_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:A`,`:K`] PASTING_LEMMA) THEN
  MAP_EVERY EXISTS_TAC [`\i:A. (f:A->B)`; `U:A->A->bool`; `topspace top:A->bool`] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `(g:A->A->B) i` THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY; IN_INTER];
    ASM_MESON_TAC[]]);;

(* Local agreement with a cut-off flow on an open neighbourhood. *)

let MCF_LOCAL_AGREE = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) a b x0.
        mcf_hyp top atlas X J Fe /\ interval[a,b] SUBSET J /\ x0 IN topspace top
        ==> ?chi K U.
              mfl_hyp top atlas (\t x. chi x % X t x) J K /\
              open_in top U /\ x0 IN U /\ U SUBSET topspace top /\
              (!s t x. s IN interval[a,b] /\ t IN interval[a,b] /\ x IN U
                       ==> mfl_flow top atlas X s t x =
                           mfl_flow top atlas (\t x. chi x % X t x) s t x /\
                           chi(mfl_flow top atlas X s t x) = &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `a:real^1`; `b:real^1`; `abs((Fe:A->real) x0) + &1`] MCF_FLOW_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `M':real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "one") (LABEL_TAC "ag"))))))) THEN
  MAP_EVERY EXISTS_TAC [`chi:A->real`; `K:A->bool`;
    `{x:A | x IN topspace top /\ abs((Fe:A->real) x) < abs(Fe x0) + &1}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MCF_SUBLEVEL_OPEN THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                          `J:real^1->bool`] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`; `x:A`] THEN STRIP_TAC THEN
  USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `t:real^1`; `x:A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `gamma:real^1->A` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "one" MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MFL_CURVE_IN THEN
  MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `X:real->A->real^N`;
                        `segment[s:real^1,t]`] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

(* A compact time window containing s and a ball around t0. *)

let MCF_TIME_NBHD = prove
 (`!J (s:real^1) t0.
        open J /\ is_interval J /\ s IN J /\ t0 IN J
        ==> ?e a b. &0 < e /\ interval[a,b] SUBSET J /\ s IN interval[a,b] /\
                    ball(t0,e) SUBSET interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `t0:real^1`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `lift(drop t0 - e) IN J /\ lift(drop t0 + e) IN (J:real^1->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_CBALL; dist; NORM_1; DROP_SUB; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `lift(min (drop s) (drop t0 - e))`;
                        `lift(max (drop s) (drop t0 + e))`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `x:real^1` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [IS_INTERVAL_1]) THEN
    MAP_EVERY EXISTS_TAC [`if drop s <= drop t0 - e then s else lift(drop t0 - e)`;
                          `if drop t0 + e <= drop s then s else lift(drop t0 + e)`] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_BALL; IN_INTERVAL_1; LIFT_DROP; dist; NORM_1; DROP_SUB] THEN
    REAL_ARITH_TAC]);;

(* Continuity and smoothness of the time-s-to-t maps. *)

let MCF_FLOW_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) s t.
        mcf_hyp top atlas X J Fe /\ s IN J /\ t IN J
        ==> continuous_map (top,top) (mfl_flow top atlas X s t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MCF_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x0:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`J:real^1->bool`; `s:real^1`; `s:real^1`; `t:real^1`] MCF_WINDOW) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mcf_hyp]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `lift(min (drop s) (min (drop s) (drop t)))`;
                 `lift(max (drop s) (max (drop s) (drop t)))`;
                 `x0:A`] MCF_LOCAL_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`U:A->bool`;
    `mfl_flow top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x) s t`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFL_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let MCF_FLOW_SMOOTH_MAP = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) s t.
        mcf_hyp top atlas X J Fe /\ s IN J /\ t IN J
        ==> mfd_smooth_map atlas atlas (topspace top) (mfl_flow top atlas X s t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[mcf_hyp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace top:A->bool`; `mfl_flow top atlas (X:real->A->real^N) s t`]
    MFDD_SMOOTH_MAP_LOCAL) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MCF_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x0:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`J:real^1->bool`; `s:real^1`; `s:real^1`; `t:real^1`] MCF_WINDOW) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[mcf_hyp]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `lift(min (drop s) (min (drop s) (drop t)))`;
                 `lift(max (drop s) (max (drop s) (drop t)))`;
                 `x0:A`] MCF_LOCAL_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFDD_SMOOTH_MAP_EQ THEN
  EXISTS_TAC `top:A topology` THEN
  EXISTS_TAC `mfl_flow top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x) s t` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFL_FLOW_SMOOTH_MAP THEN
  MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `K:A->bool`] THEN ASM_REWRITE_TAC[]);;

let MCF_FLOW_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) s t.
        mcf_hyp top atlas X J Fe /\ s IN J /\ t IN J
        ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                       (mfl_flow top atlas X s t) (mfl_flow top atlas X t s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE; homeomorphic_maps] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MCF_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MCF_FLOW_CONTINUOUS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                   `s:real^1`; `t:real^1`; `s:real^1`; `x:A`] MCF_FLOW_COCYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MCF_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                   `t:real^1`; `s:real^1`; `t:real^1`; `x:A`] MCF_FLOW_COCYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MCF_FLOW_REFL THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MCF_FLOW_SMOOTH_MAP THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MCF_FLOW_SMOOTH_MAP THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`] THEN ASM_REWRITE_TAC[]]);;

(* The chart form of the time derivative. *)

let MCF_FLOW_DERIV = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) c s t x.
        mcf_hyp top atlas X J Fe /\ c IN atlas /\ s IN J /\ t IN J /\ x IN topspace top /\
        mfl_flow top atlas X s t x IN FST c
        ==> ((\r. SND c (mfl_flow top atlas X s r x)) has_vector_derivative
             mfd_vrep atlas (X (drop t)) c (SND c (mfl_flow top atlas X s t x))) (at t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mcf_hyp]) THEN
  MP_TAC(ISPECL [`J:real^1->bool`; `s:real^1`; `t:real^1`] MCF_TIME_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `a:real^1` (X_CHOOSE_THEN `b:real^1`
    STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(t:real^1) IN interval[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; CENTRE_IN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `a:real^1`; `b:real^1`; `x:A`] MCF_LOCAL_AGREE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ag")))))))) THEN
  USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `t:real^1`; `x:A`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "e1" o SYM) (LABEL_TAC "e2"))] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `J:real^1->bool`;
                 `K:A->bool`] MFLOW_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:(A->bool)#(A->real^N)`; `s:real^1`; `t:real^1`; `x:A`] o
             CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "dY")] THEN
  SUBGOAL_THEN
   `mfd_vrep atlas (\y. (chi:A->real) y % (X:real->A->real^N) (drop t) y)
      (c:(A->bool)#(A->real^N)) (SND c (mfl_flow top atlas X s t x)) =
    mfd_vrep atlas (X (drop t)) c (SND c (mfl_flow top atlas X s t x))`
  (LABEL_TAC "vr") THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `chi:A->real`; `(X:real->A->real^N) (drop t)`;
                   `c:(A->bool)#(A->real^N)`;
                   `SND (c:(A->bool)#(A->real^N))
                      (mfl_flow top atlas (X:real->A->real^N) s t x)`] MCF_VREP_CMUL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `mfl_flow top atlas (X:real->A->real^N) s t x` o
               CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "e2" SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC
   [`\r. SND (c:(A->bool)#(A->real^N))
           (mfl_flow top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x) s r x)`;
    `e:real`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN
    USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `r:real^1`; `x:A`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(t:real^1,e) SUBSET interval[a,b]` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    USE_THEN "dY" MP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "e1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "vr" (fun th -> REWRITE_TAC[th])]);;

(* Joint smoothness in charts, with open domain. *)

let MCF_JOINT_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real) c c' s.
        mcf_hyp top atlas X J Fe /\ c IN atlas /\ c' IN atlas /\ s IN J
        ==> open {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                  mfl_flow top atlas X s t (chart_inv c y) IN FST c'} /\
            smooth_map_on
              {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                               mfl_flow top atlas X s t (chart_inv c y) IN FST c'}
              (\z. SND c' (mfl_flow top atlas X s (fstcart z) (chart_inv c (sndcart z))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mcf_hyp]) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `D = {pastecart t y | t IN J /\ y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                         mfl_flow top atlas (X:real->A->real^N) s t (chart_inv c y) IN
                         FST (c':(A->bool)#(A->real^N))}` THEN
  SUBGOAL_THEN
   `!z. z IN D
        ==> ?W. open W /\ z IN W /\ W SUBSET D /\
                smooth_map_on W
                  (\z. SND (c':(A->bool)#(A->real^N))
                         (mfl_flow top atlas (X:real->A->real^N) s (fstcart z)
                            (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))))`
  ASSUME_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `open(D:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_MESON_TAC[]] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN EXPAND_TAC "D" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^1` (X_CHOOSE_THEN `y0:real^N`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `y0:real^N`] MCF_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real^1->bool`; `s:real^1`; `t0:real^1`] MCF_TIME_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `a:real^1` (X_CHOOSE_THEN `b:real^1`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `X:real->A->real^N`; `J:real^1->bool`; `Fe:A->real`;
                 `a:real^1`; `b:real^1`; `chart_inv (c:(A->bool)#(A->real^N)) y0`]
    MCF_LOCAL_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `chi:A->real` (X_CHOOSE_THEN `K:A->bool`
    (X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ag")))))))) THEN
  SUBGOAL_THEN
   `!t y. t IN ball(t0,e) /\ y IN IMAGE (SND c) (FST c INTER U)
          ==> t IN J /\ y IN IMAGE (SND c) (FST c) /\
              mfl_flow top atlas (X:real->A->real^N) s t (chart_inv c y) =
              mfl_flow top atlas (\t x. (chi:A->real) x % X t x) s t
                (chart_inv (c:(A->bool)#(A->real^N)) y)`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:A`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(t:real^1) IN interval[a,b]` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(t0:real^1,e) SUBSET interval[a,b]` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `interval[a:real^1,b] SUBSET J` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `p:A` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) (SND c (p:A)) = p` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "ag" (MP_TAC o SPECL [`s:real^1`; `t:real^1`; `p:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)]];
    ALL_TAC] THEN
  REMOVE_THEN "ag" (K ALL_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `\t x. (chi:A->real) x % (X:real->A->real^N) t x`; `J:real^1->bool`;
                 `K:A->bool`; `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
                 `s:real^1`] MFL_JOINT_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC
   `{pastecart t y | t IN J /\ y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                     mfl_flow top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x) s t
                       (chart_inv c y) IN FST (c':(A->bool)#(A->real^N))} INTER
    (ball(t0:real^1,e) PCROSS IMAGE (SND c) (FST c INTER (U:A->bool)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    SUBGOAL_THEN
     `(y0:real^N) IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER (U:A->bool))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      EXISTS_TAC `chart_inv (c:(A->bool)#(A->real^N)) y0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_PASTECART_THM; PASTECART_IN_PCROSS] THEN
    USE_THEN "pt" (MP_TAC o SPECL [`t0:real^1`; `y0:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    EXPAND_TAC "D" THEN
    REWRITE_TAC[SUBSET; IN_INTER; FORALL_PASTECART; IN_ELIM_PASTECART_THM;
                PASTECART_IN_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "pt" (MP_TAC o SPECL [`t:real^1`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2)] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\z. SND (c':(A->bool)#(A->real^N))
            (mfl_flow top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x) s
               (fstcart z) (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_INTER; FORALL_PASTECART; IN_ELIM_PASTECART_THM; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`t:real^1`; `y:real^N`] THEN STRIP_TAC THEN
      USE_THEN "pt" (MP_TAC o SPECL [`t:real^1`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2)] THEN
      REFL_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC
       `{pastecart t y | t IN J /\ y IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                         mfl_flow top atlas (\t x. (chi:A->real) x % (X:real->A->real^N) t x)
                           s t (chart_inv c y) IN FST (c':(A->bool)#(A->real^N))}` THEN
      ASM_REWRITE_TAC[INTER_SUBSET]]]);;

(* MCF_FLOW_GEN: the conclusions of MFLOW_GEN (without the compact support *)
(* clause) for a field with a proper escape function, plus the integral    *)
(* curves and the openness of the joint domain in charts.                  *)

let MCF_FLOW_GEN = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) (X:real->A->real^N) J (Fe:A->real).
        mcf_hyp top atlas X J Fe
        ==> (!s t x. s IN J /\ t IN J /\ x IN topspace top
                     ==> mfl_flow top atlas X s t x IN topspace top /\
                         ?gamma. mfl_curve top atlas X (segment[s,t]) gamma /\
                                 gamma s = x /\ gamma t = mfl_flow top atlas X s t x) /\
            (!s x. s IN J /\ x IN topspace top ==> mfl_flow top atlas X s s x = x) /\
            (!s r t x. s IN J /\ r IN J /\ t IN J /\ x IN topspace top
                       ==> mfl_flow top atlas X r t (mfl_flow top atlas X s r x) =
                           mfl_flow top atlas X s t x) /\
            (!s t. s IN J /\ t IN J
                   ==> mfd_diffeo top atlas (topspace top) top atlas (topspace top)
                         (mfl_flow top atlas X s t) (mfl_flow top atlas X t s)) /\
            (!c s t x. c IN atlas /\ s IN J /\ t IN J /\ x IN topspace top /\
                       mfl_flow top atlas X s t x IN FST c
                       ==> ((\r. SND c (mfl_flow top atlas X s r x)) has_vector_derivative
                            mfd_vrep atlas (X (drop t)) c
                              (SND c (mfl_flow top atlas X s t x))) (at t)) /\
            (!c c' s. c IN atlas /\ c' IN atlas /\ s IN J
                      ==> open {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                                mfl_flow top atlas X s t (chart_inv c y) IN
                                                FST c'} /\
                          smooth_map_on
                            {pastecart t y | t IN J /\ y IN IMAGE (SND c) (FST c) /\
                                             mfl_flow top atlas X s t (chart_inv c y) IN
                                             FST c'}
                            (\z. SND c' (mfl_flow top atlas X s (fstcart z)
                                           (chart_inv c (sndcart z)))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THENL
   [MATCH_MP_TAC MCF_FLOW_CURVE_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`];
    MATCH_MP_TAC MCF_FLOW_REFL THEN MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`];
    MATCH_MP_TAC MCF_FLOW_COCYCLE THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`];
    MATCH_MP_TAC MCF_FLOW_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`];
    MATCH_MP_TAC MCF_FLOW_DERIV THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `Fe:A->real`];
    MATCH_MP_TAC MCF_JOINT_SMOOTH THEN EXISTS_TAC `Fe:A->real`] THEN
  ASM_REWRITE_TAC[]);;

