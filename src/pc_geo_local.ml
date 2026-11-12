(* ========================================================================= *)
(* pc_geo_local: geodesics at chart level.  The geodesic equation is chart  *)
(* independent (naturality of the Christoffel symbols, LCHRISTOFFEL_PULLBACK *)
(* of pc_lrg), local existence and uniqueness and smoothness from the ODE    *)
(* package (pc_ode_vf), constant speed, affine reparametrization, the link  *)
(* with the geodesic spray, and the flat teeth tests.  Its theorems belong   *)
(* to the geodesics API pc_geo_iface.                                        *)
(*                                                                           *)
(* Elementary facts and a calculus lemma (derivative of                      *)
(* r |-> Dh(y r)(v r)).                                                       *)
(* ========================================================================= *)

needs "src/pc_geo_defs.ml";;
needs "src/pc_ode_vf.ml";;

prioritize_real();;
type_invention_error := true;;

let MFD_GEODESIC_CONST = prove
 (`!top atlas (g:A->real^N^N) (x:A).
        x IN topspace top
        ==> mfd_geodesic (top,atlas) g (\t. x) (:real) /\
            !t. mfd_vel atlas (\t. x) t = vec 0`,
  SIMP_TAC[MFD_GEODESIC_CONST_PROVED; mfd_vel; VECTOR_DERIVATIVE_CONST_AT]);;

let MFD_GEODESIC_SUBINTERVAL = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J J'.
        mfd_geodesic (top,atlas) g gamma J /\
        is_realinterval J' /\ real_open J' /\ J' SUBSET J
        ==> mfd_geodesic (top,atlas) g gamma J'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_geodesic] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
    EXISTS_TAC `J:real->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v:real->real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Vector derivatives of finite sums. *)

let GEOL_HAS_VECTOR_DERIVATIVE_VSUM = prove
 (`!(f:A->real^1->real^N) f' k net.
        FINITE k /\ (!i. i IN k ==> (f i has_vector_derivative f' i) net)
        ==> ((\x. vsum k (\i. f i x)) has_vector_derivative vsum k f') net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\h:real^1. drop h % vsum k (f':A->real^N)) =
    (\h. vsum k (\i. drop h % f' i))`
  SUBST1_TAC THENL [ASM_SIMP_TAC[VSUM_LMUL]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_VSUM THEN ASM_REWRITE_TAC[]);;

(* A linear map on real^N in terms of its values on the standard basis. *)

let GEOL_LINEAR_EXPAND = prove
 (`!(f:real^N->real^M) w.
        linear f
        ==> f w = vsum (1..dimindex(:N)) (\i. drop(lift(w$i)) % f(basis i))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LIFT_DROP; LINEAR_CMUL]);;

(* The derivative of r |-> Dh(y r)(v r) along a curve: the second derivative *)
(* term plus Dh applied to the derivative of v.                              *)

let GEOL_FRECHET_ALONG = prove
 (`!s (h:real^N->real^M) (y:real^1->real^N) (v:real^1->real^N) y' v' t.
        open s /\ smooth_map_on s h /\ y t IN s /\
        (y has_vector_derivative y') (at t) /\
        (v has_vector_derivative v') (at t)
        ==> ((\r. frechet_derivative h (at (y r)) (v r)) has_vector_derivative
             (frechet_derivative (\z. frechet_derivative h (at z) (v t))
                                 (at (y t)) y' +
              frechet_derivative h (at (y t)) v')) (at t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN s ==> linear(frechet_derivative (h:real^N->real^M) (at z))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[LINEAR_FRECHET_DERIVATIVE; SMOOTH_MAP_ON_DIFFERENTIABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ((\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
         has_derivative
         frechet_derivative (\z. frechet_derivative h (at z) (basis i))
                            (at ((y:real^1->real^N) t))) (at (y t))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  (* the derivative of the expanded form *)
  SUBGOAL_THEN
   `((\r. vsum (1..dimindex(:N))
            (\i. drop(lift(((v:real^1->real^N) r)$i)) %
                 frechet_derivative (h:real^N->real^M) (at (y r)) (basis i)))
     has_vector_derivative
     vsum (1..dimindex(:N))
       (\i. drop(lift((v t)$i)) %
            frechet_derivative
              (\z. frechet_derivative h (at z) (basis i)) (at (y t)) y' +
            drop(lift((v':real^N)$i)) % frechet_derivative h (at (y t)) (basis i)))
    (at t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_HAS_VECTOR_DERIVATIVE_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\x:real^1 w:real^M. drop x % w`;
      `\r. lift(((v:real^1->real^N) r)$i)`;
      `\r. frechet_derivative (h:real^N->real^M) (at ((y:real^1->real^N) r))
                              (basis i)`;
      `lift((v':real^N)$i)`;
      `frechet_derivative
         (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
         (at ((y:real^1->real^N) t)) y'`;
      `t:real^1`] HAS_VECTOR_DERIVATIVE_BILINEAR_AT) THEN
    BETA_TAC THEN REWRITE_TAC[BILINEAR_DROP_MUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_LIFT_COMPONENT_AT THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`y:real^1->real^N`;
        `\z. frechet_derivative (h:real^N->real^M) (at z) (basis i)`;
        `y':real^N`;
        `frechet_derivative
           (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
           (at ((y:real^1->real^N) t))`;
        `t:real^1`; `(:real^1)`] GRGD_VECTOR_DERIVATIVE_CHAIN) THEN
      ASM_REWRITE_TAC[WITHIN_UNIV; o_DEF]];
    ALL_TAC] THEN
  (* identify the derivative *)
  SUBGOAL_THEN
   `vsum (1..dimindex(:N))
       (\i. drop(lift(((v:real^1->real^N) t)$i)) %
            frechet_derivative
              (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
              (at ((y:real^1->real^N) t)) y' +
            drop(lift((v':real^N)$i)) % frechet_derivative h (at (y t)) (basis i)) =
    frechet_derivative (\z. frechet_derivative h (at z) (v t)) (at (y t)) y' +
    frechet_derivative h (at (y t)) v'`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN BINOP_TAC THENL
     [ALL_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN
     `((\z. frechet_derivative (h:real^N->real^M) (at z) ((v:real^1->real^N) t))
       has_derivative
       (\u. vsum (1..dimindex(:N))
              (\i. drop(lift((v t)$i)) %
                   frechet_derivative
                     (\z. frechet_derivative h (at z) (basis i))
                     (at ((y:real^1->real^N) t)) u))) (at (y t))`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC
       `\z. vsum (1..dimindex(:N))
              (\i. drop(lift(((v:real^1->real^N) t)$i)) %
                   frechet_derivative (h:real^N->real^M) (at z) (basis i))` THEN
      EXISTS_TAC `s:real^N->bool` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
        REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(INST
       [`\i:num u:real^N. drop(lift(((v:real^1->real^N) t)$i)) %
                  frechet_derivative
                    (\z. frechet_derivative (h:real^N->real^M) (at z) (basis i))
                    (at ((y:real^1->real^N) t)) u`,`f':num->real^N->real^M`]
       (ISPECL
       [`\i:num z. drop(lift(((v:real^1->real^N) t)$i)) %
                   frechet_derivative (h:real^N->real^M) (at z) (basis i)`;
        `at ((y:real^1->real^N) t)`; `1..dimindex(:N)`] HAS_DERIVATIVE_VSUM)) THEN
      BETA_TAC THEN REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)])];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC
   `\r. vsum (1..dimindex(:N))
          (\i. drop(lift(((v:real^1->real^N) r)$i)) %
               frechet_derivative (h:real^N->real^M) (at (y r)) (basis i))` THEN
  SUBGOAL_THEN `(y:real^1->real^N) continuous at t` MP_TAC THENL
   [ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; differentiable;
                  has_vector_derivative]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(y:real^1->real^N) t` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_LINEAR_EXPAND THEN
  REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
    `!z:real^N. z IN s ==> linear(frechet_derivative (h:real^N->real^M) (at z))`)
    (concl th))) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_SIMP_TAC[]);;

(* Linear maps are smooth on open sets. *)

let GEOL_SMOOTH_LINEAR = prove
 (`!s (f:real^M->real^N). open s /\ linear f ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `f:real^M->real^N`]
    SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

(* The geodesic spray of a metric field is smooth on U x real^N. *)

let GEOL_SPRAY_SMOOTH = prove
 (`!U (G:real^N->real^N^N).
        metric_field U G ==> smooth_map_on (U PCROSS (:real^N)) (geo_spray G)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `open ((U:real^N->bool) PCROSS (:real^N))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\z:real^(N,N)finite_sum.
      pastecart (sndcart z)
       (--(vsum (1..dimindex(:N))
            (\i. drop(lift((sndcart z)$i)) %
                 vsum (1..dimindex(:N))
                  (\j. drop(lift((sndcart z)$j)) %
                       christoffel (G:real^N->real^N^N) (fstcart z)
                                   (basis i) (basis j)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                geo_spray; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `u:real^N`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`]
      CHRISTOFFEL_BILINEAR) THEN
    ASM_REWRITE_TAC[bilinear] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\w. christoffel (G:real^N->real^N^N) y w u`; `u:real^N`]
      GEOL_LINEAR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`\w. christoffel (G:real^N->real^N^N) y (basis i) w`;
                   `u:real^N`] GEOL_LINEAR_EXPAND) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM o_DEF; ETA_AX] THEN MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. smooth_map_on ((U:real^N->bool) PCROSS (:real^N))
          (\z:real^(N,N)finite_sum. lift((sndcart z)$k))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(\z:real^(N,N)finite_sum. lift((sndcart z)$k)) =
      (\x:real^N. lift(x$k)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_COMPOSE THEN
    REWRITE_TAC[LINEAR_SNDCART; LINEAR_LIFT_COMPONENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(U:real^N->bool) PCROSS (:real^N)`;
                 `\x:real^1 w:real^N. drop x % w`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[BILINEAR_DROP_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(U:real^N->bool) PCROSS (:real^N)`;
                 `\x:real^1 w:real^N. drop x % w`] SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[BILINEAR_DROP_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\z:real^(N,N)finite_sum.
       christoffel (G:real^N->real^N^N) (fstcart z) (basis i) (basis j)) =
    (\y. christoffel G y (basis i) (basis j)) o fstcart`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[LRG_CHRISTOFFEL_SMOOTH] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
    SIMP_TAC[];
    MATCH_MP_TAC GEOL_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_FSTCART]]);;

(* ========================================================================= *)
(* Chart changes along curves; the geodesic equation is chart                *)
(* independent (MFD_GEODESIC_VEL_CHART, MFD_GEODESIC_CHART_TRANS).           *)
(* ========================================================================= *)

(* Chart transition facts for charts given as pairs. *)

let GEOL_CHART_TRANS_FACTS = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) c'.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas
        ==> open (IMAGE (SND c) (FST c INTER FST c')) /\
            smooth_map_on (IMAGE (SND c) (FST c INTER FST c')) (chart_trans c c') /\
            diffeomorphism_on (IMAGE (SND c) (FST c INTER FST c'))
                              (IMAGE (SND c') (FST c INTER FST c'))
                              (chart_trans c c') (chart_trans c' c) /\
            (!x. x IN FST c ==> chart_trans c c' (SND c x) = SND c' x) /\
            (!x. x IN FST c INTER FST c'
                 ==> (chart_trans c c' has_derivative chart_jac c c' x)
                     (at (SND c x)))`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(GSYM(ISPEC `c:(A->bool)#(A->real^N)` PAIR)) THEN
  SUBST1_TAC(GSYM(ISPEC `c':(A->bool)#(A->real^N)` PAIR)) THEN
  PURE_REWRITE_TAC[FST; SND] THEN STRIP_TAC THEN
  ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN; CHART_TRANS_SMOOTH; CHART_TRANS_DIFFEO;
                CHART_TRANS_AT; CHART_TRANS_HAS_DERIVATIVE]);;

(* Times at which a continuous curve lies in an open set form an open set. *)

let GEOL_CURVE_OPEN_TIMES = prove
 (`!top (gamma:real->A) J W.
        real_open J /\ continuous_map (subtopology euclideanreal J,top) gamma /\
        open_in top W
        ==> real_open {s | s IN J /\ gamma s IN W}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OPEN_IN] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `J:real->bool` THEN
  ASM_REWRITE_TAC[GSYM REAL_OPEN_IN] THEN
  MP_TAC(ISPECL [`gamma:real->A`; `subtopology euclideanreal J`; `top:A topology`;
                 `W:A->bool`] OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]);;

(* Near a time t in J at which gamma t lies in the open set W, the curve     *)
(* stays in W.                                                              *)

let GEOL_CURVE_NEAR = prove
 (`!top (gamma:real->A) J W t.
        real_open J /\ continuous_map (subtopology euclideanreal J,top) gamma /\
        open_in top W /\ t IN J /\ gamma t IN W
        ==> ?d. &0 < d /\
                !s. abs(s - t) < d ==> s IN J /\ gamma s IN W`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`; `W:A->bool`]
    GEOL_CURVE_OPEN_TIMES) THEN
  ASM_REWRITE_TAC[real_open; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[]);;

(* First-order chart change of a curve velocity. *)

let GEOL_CHART_CHANGE_VEL = prove
 (`!top atlas (gamma:real->A) J (c:(A->bool)#(A->real^N)) c' v t.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ c' IN atlas /\
        real_open J /\ continuous_map (subtopology euclideanreal J,top) gamma /\
        t IN J /\ gamma t IN FST c INTER FST c' /\
        ((\s. SND c (gamma(drop s))) has_vector_derivative v) (at (lift t))
        ==> ((\s. SND c' (gamma(drop s))) has_vector_derivative
             chart_jac c c' (gamma t) v) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                 `FST(c:(A->bool)#(A->real^N)) INTER FST(c':(A->bool)#(A->real^N))`;
                 `t:real`] GEOL_CURVE_NEAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_MESON_TAC[MFDM_CHART];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `chart_trans (c:(A->bool)#(A->real^N)) c' o
              (\s. SND c ((gamma:real->A)(drop s)))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!x:A. x IN FST (c:(A->bool)#(A->real^N))
             ==> chart_trans c c' (SND c x) = SND (c':(A->bool)#(A->real^N)) x`)
      (concl th))) THEN
    SUBGOAL_THEN `abs(drop s - t) < d` (fun th -> ASM_MESON_TAC[th; IN_INTER]) THEN
    UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MATCH_MP_TAC GRGD_VECTOR_DERIVATIVE_CHAIN THEN
  ASM_REWRITE_TAC[WITHIN_UNIV; LIFT_DROP] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MFD_GEODESIC_VEL_CHART = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas /\
        t IN J /\ gamma t IN FST c
        ==> ((\s. SND c (gamma(drop s))) has_vector_derivative
             chart_jac (chart_at atlas (gamma t)) c (gamma t)
                       (mfd_vel atlas gamma t)) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [mfd_geodesic]) THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [continuous_map] o
      check (fun th -> can (term_match []
        `continuous_map (subtopology euclideanreal J,top:A topology) gamma`)
        (concl th))) THEN
    ASM_SIMP_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool)
                                        ((gamma:real->A) t)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real->real^N` (MP_TAC o SPEC `t:real`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_vel atlas (gamma:real->A) t = (v0:real->real^N) t`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_vel] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC GEOL_CHART_CHANGE_VEL THEN
  MAP_EVERY EXISTS_TAC
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
  ASM_REWRITE_TAC[IN_INTER]);;

(* The geodesic equation transforms correctly between charts (naturality of *)
(* the Christoffel symbols).                                                *)

let MFD_GEODESIC_CHART_TRANS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c c' v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ c' IN atlas /\ real_open J /\
        continuous_map (subtopology euclideanreal J,top) gamma /\
        (!t. t IN J /\ gamma t IN FST c
             ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t)
                 (at (lift t)) /\
                 ((\s. v(drop s)) has_vector_derivative
                  --(christoffel (metric_local atlas c g) (SND c (gamma t))
                                 (v t) (v t))) (at (lift t)))
        ==> !t. t IN J /\ gamma t IN FST c INTER FST c'
                ==> ((\s. SND c' (gamma(drop s))) has_vector_derivative
                     chart_jac c c' (gamma t) (v t)) (at (lift t)) /\
                    ((\s. chart_jac c c' (gamma(drop s)) (v(drop s)))
                     has_vector_derivative
                     --(christoffel (metric_local atlas c' g) (SND c' (gamma t))
                          (chart_jac c c' (gamma t) (v t))
                          (chart_jac c c' (gamma t) (v t)))) (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GEOL_CHART_CHANGE_VEL THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`]
    GEOL_CHART_TRANS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[chart_jac] THEN
  ABBREV_TAC `tau = chart_trans (c:(A->bool)#(A->real^N)) c'` THEN
  ABBREV_TAC `W = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c INTER FST (c':(A->bool)#(A->real^N)))` THEN
  ABBREV_TAC `y = SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t)` THEN
  SUBGOAL_THEN `(y:real^N) IN W` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["y"; "W"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the derivative from the calculus lemma *)
  MP_TAC(ISPECL
   [`W:real^N->bool`; `tau:real^N->real^N`;
    `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))`;
    `\s. (v:real->real^N)(drop s)`; `(v:real->real^N) t`;
    `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    (y:real^N) ((v:real->real^N) t) (v t))`;
    `lift t`] GEOL_FRECHET_ALONG) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN
  (* identify it *)
  SUBGOAL_THEN `linear(frechet_derivative (tau:real^N->real^N) (at y))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (tau:real^N->real^N) (at y)
      (christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                   y ((v:real->real^N) t) (v t)) =
    christoffel (metric_local atlas c' g) (SND c' ((gamma:real->A) t))
      (frechet_derivative tau (at y) (v t))
      (frechet_derivative tau (at y) (v t)) +
    dd2 tau y (v t) (v t)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                  (y:real^N) ((v:real->real^N) t) (v t) =
      christoffel (mpullback (tau:real^N->real^N) (metric_local atlas c' g))
                  y (v t) (v t)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      EXPAND_TAC "tau" THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                     `FST(c':(A->bool)#(A->real^N))`;
                     `SND(c':(A->bool)#(A->real^N))`; `g:A->real^N^N`; `x:A`]
        METRIC_LOCAL_TRANS) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    SUBGOAL_THEN `SND (c':(A->bool)#(A->real^N)) ((gamma:real->A) t) = tau(y:real^N)`
    SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!x:A. x IN FST (c:(A->bool)#(A->real^N))
               ==> (tau:real^N->real^N) (SND c x) = SND (c':(A->bool)#(A->real^N)) x`)
        (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LCHRISTOFFEL_PULLBACK THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (SND (c':(A->bool)#(A->real^N)))
             (FST (c:(A->bool)#(A->real^N)) INTER FST (c':(A->bool)#(A->real^N)))`;
      `W:real^N->bool`; `chart_trans (c':(A->bool)#(A->real^N)) c`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `g:A->real^N^N`] RIEMANNIAN_METRIC_OVERLAP) THEN
    ASM_REWRITE_TAC[PAIR] THEN REWRITE_TAC[INTER_COMM];
    ALL_TAC] THEN
  REWRITE_TAC[dd2] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LINEAR_NEG] THEN
  MATCH_MP_TAC(MESON[] `(a:real^N) = b ==> (f has_vector_derivative a) net
                                         ==> (f has_vector_derivative b) net`) THEN
  VECTOR_ARITH_TAC);;

(* ========================================================================= *)
(* Solutions of the spray equation in a chart give geodesics;                *)
(* local existence of geodesics (MFD_GEODESIC_EXISTS_LOCAL).                 *)
(* ========================================================================= *)

let GEOL_IN_PCROSS = prove
 (`!(s:real^M->bool) (t:real^N->bool) z.
        z IN s PCROSS t <=> fstcart z IN s /\ sndcart z IN t`,
  MESON_TAC[PASTECART_FST_SND; PASTECART_IN_PCROSS]);;

(* A solution Z of z' = geo_spray G z with first component in the chart     *)
(* image gives, through the chart, a geodesic whose chart velocity is the   *)
(* second component.                                                         *)

let GEOL_SPRAY_GEODESIC = prove
 (`!top atlas (g:A->real^N^N) (c:(A->bool)#(A->real^N)) J
    (Z:real^1->real^(N,N)finite_sum).
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ is_realinterval J /\ real_open J /\
        (!t. t IN J
             ==> fstcart(Z(lift t)) IN IMAGE (SND c) (FST c) /\
                 (Z has_vector_derivative
                  geo_spray (metric_local atlas c g) (Z(lift t))) (at (lift t)))
        ==> mfd_geodesic (top,atlas) g (\t. chart_inv c (fstcart(Z(lift t)))) J /\
            !t. t IN J
                ==> ((\s. SND c (chart_inv c (fstcart(Z(lift(drop s))))))
                     has_vector_derivative sndcart(Z(lift t))) (at (lift t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. t IN J
        ==> chart_inv c (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t)))
            IN FST (c:(A->bool)#(A->real^N)) /\
            SND c (chart_inv c (fstcart(Z(lift t)))) = fstcart(Z(lift t))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* derivatives of the two components *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> ((fstcart o (Z:real^1->real^(N,N)finite_sum)) has_vector_derivative
             sndcart(Z(lift t))) (at (lift t)) /\
            ((sndcart o Z) has_vector_derivative
             --(christoffel (metric_local atlas c (g:A->real^N^N))
                  (fstcart(Z(lift t))) (sndcart(Z(lift t))) (sndcart(Z(lift t)))))
            (at (lift t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (term_match [] `!t. t IN J
             ==> fstcart((Z:real^1->real^(N,N)finite_sum)(lift t))
                 IN IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) /\
                 (Z has_vector_derivative
                  geo_spray (metric_local atlas c (g:A->real^N^N)) (Z(lift t)))
                 (at (lift t))`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`Z:real^1->real^(N,N)finite_sum`; `fstcart:real^(N,N)finite_sum->real^N`;
        `geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                   ((Z:real^1->real^(N,N)finite_sum)(lift t))`;
        `fstcart:real^(N,N)finite_sum->real^N`; `lift t`; `(:real^1)`]
       GRGD_VECTOR_DERIVATIVE_CHAIN);
      MP_TAC(ISPECL
       [`Z:real^1->real^(N,N)finite_sum`; `sndcart:real^(N,N)finite_sum->real^N`;
        `geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                   ((Z:real^1->real^(N,N)finite_sum)(lift t))`;
        `sndcart:real^(N,N)finite_sum->real^N`; `lift t`; `(:real^1)`]
       GRGD_VECTOR_DERIVATIVE_CHAIN)] THEN
    ASM_REWRITE_TAC[WITHIN_UNIV] THEN
    REWRITE_TAC[geo_spray; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  (* local form of the chart representation *)
  SUBGOAL_THEN
   `!t. t IN J
        ==> ((\s. SND (c:(A->bool)#(A->real^N))
                    (chart_inv c (fstcart((Z:real^1->real^(N,N)finite_sum)
                                            (lift(drop s))))))
             has_vector_derivative sndcart(Z(lift t))) (at (lift t)) /\
            ((\s. sndcart(Z(lift(drop s)))) has_vector_derivative
             --(christoffel (metric_local atlas c (g:A->real^N^N))
                  (SND c (chart_inv c (fstcart(Z(lift t)))))
                  (sndcart(Z(lift t))) (sndcart(Z(lift t)))))
            (at (lift t))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real` o GEN_REWRITE_RULE I [real_open] o
      check (fun th -> can (term_match [] `real_open (J:real->bool)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN
     `SND (c:(A->bool)#(A->real^N))
        (chart_inv c (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t)))) =
      fstcart(Z(lift t))`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SUBGOAL_THEN `(\s. sndcart((Z:real^1->real^(N,N)finite_sum) s)) = sndcart o Z`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ASM_SIMP_TAC[]]] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `fstcart o (Z:real^1->real^(N,N)finite_sum)` THEN
    EXISTS_TAC `d:real` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ALL_TAC;
      ASM_SIMP_TAC[]] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `drop s IN (J:real->bool)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `dist(s:real^1,lift t) < d` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP];
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
        can (term_match [] `!t. t IN J
             ==> chart_inv c (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t)))
                 IN FST (c:(A->bool)#(A->real^N)) /\
                 SND c (chart_inv c (fstcart(Z(lift t)))) = fstcart(Z(lift t))`)
        (concl th)))) THEN
      SIMP_TAC[LIFT_DROP]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  (* continuity *)
  SUBGOAL_THEN
   `continuous_map (subtopology euclideanreal J,top)
      (\t. chart_inv (c:(A->bool)#(A->real^N))
             (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN] THEN
    SUBGOAL_THEN
     `(\t. chart_inv (c:(A->bool)#(A->real^N))
             (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t)))) o drop =
      chart_inv c o (fstcart o Z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean
                  (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real` THEN DISCH_TAC THEN
        MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `\h:real^1. drop h %
                      sndcart((Z:real^1->real^(N,N)finite_sum)(lift t))` THEN
        REWRITE_TAC[GSYM has_vector_derivative] THEN ASM_SIMP_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC MFDD_CHART_INV_CONTINUOUS THEN
      EXISTS_TAC `atlas:((A->bool)#(A->real^N))->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_geodesic] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c':(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
    `\t. chart_inv (c:(A->bool)#(A->real^N))
           (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t)))`;
    `J:real->bool`; `c:(A->bool)#(A->real^N)`; `c':(A->bool)#(A->real^N)`;
    `\t. sndcart((Z:real^1->real^(N,N)finite_sum)(lift t))`]
   MFD_GEODESIC_CHART_TRANS) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC
   `\t. chart_jac (c:(A->bool)#(A->real^N)) c'
          (chart_inv c (fstcart((Z:real^1->real^(N,N)finite_sum)(lift t))))
          (sndcart(Z(lift t)))` THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_INTER]);;

(* Local existence: the spray flow in the preferred chart at x. *)

let MFD_GEODESIC_EXISTS_LOCAL = prove
 (`!top atlas (g:A->real^N^N) (x:A) v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top
        ==> ?e gamma. &0 < e /\
                      mfd_geodesic (top,atlas) g gamma (real_interval(--e,e)) /\
                      gamma(&0) = x /\ mfd_vel atlas gamma (&0) = v`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) x` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN atlas /\ x IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c))
                 (metric_local atlas c (g:A->real^N^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)` THEN
  ABBREV_TAC
   `X = geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
  ABBREV_TAC `z0 = pastecart (SND (c:(A->bool)#(A->real^N)) x) (v:real^N)` THEN
  SUBGOAL_THEN
   `open (D:real^(N,N)finite_sum->bool) /\
    continuously_differentiable 1 D (X:real^(N,N)finite_sum->real^(N,N)finite_sum) /\
    z0 IN D`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "X"; "z0"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`]
        GEOL_SPRAY_SMOOTH) THEN
      ASM_SIMP_TAC[smooth_map_on];
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(N,N)finite_sum->bool`; `z0:real^(N,N)finite_sum`]
    ODE_VF_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `M = ode_vf_maxint (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D z0` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^1` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> can (term_match [] `open (M:real^1->bool)`) (concl th))) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; DIST_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. t IN real_interval(--e,e) ==> lift t IN M` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[NORM_LIFT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `real_interval(--e,e)`;
                 `\s. ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                  D s z0`] GEOL_SPRAY_GEODESIC) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL; REAL_OPEN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift t` o check (fun th -> can (term_match []
      `!t. t IN (M:real^1->bool)
           ==> ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D t z0 IN D /\
               ((\s. ode_vf_flow X D s z0) has_vector_derivative
                X (ode_vf_flow X D t z0)) (at t)`) (concl th))) THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "D" THEN
    SIMP_TAC[GEOL_IN_PCROSS];
    ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\t. chart_inv (c:(A->bool)#(A->real^N))
                    (fstcart(ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                         D (lift t) z0))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 IN real_interval(--e,e)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `chart_inv (c:(A->bool)#(A->real^N))
      (fstcart(ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                           D (lift(&0)) z0)) = x`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LIFT_NUM] THEN REWRITE_TAC[SYM(ASSUME
      `pastecart (SND (c:(A->bool)#(A->real^N)) x) (v:real^N) = z0`)] THEN
    REWRITE_TAC[FSTCART_PASTECART] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_vel] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> can (term_match []
    `!t. t IN real_interval(--e,e)
         ==> ((\s. SND (c:(A->bool)#(A->real^N))
                     (chart_inv c (fstcart(ode_vf_flow
                        (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D
                        (lift(drop s)) z0))))
              has_vector_derivative
              sndcart(ode_vf_flow X D (lift t) z0)) (at (lift t))`) (concl th))) THEN
  ASM_REWRITE_TAC[LIFT_NUM] THEN REWRITE_TAC[SYM(ASSUME
      `pastecart (SND (c:(A->bool)#(A->real^N)) x) (v:real^N) = z0`)] THEN
  REWRITE_TAC[SNDCART_PASTECART]);;

(* ========================================================================= *)
(* Uniqueness of geodesics (MFD_GEODESIC_UNIQUE).                            *)
(* ========================================================================= *)

let GEOL_HAS_VECTOR_DERIVATIVE_PASTECART = prove
 (`!(f:real^1->real^M) (g:real^1->real^N) f' g' net.
        (f has_vector_derivative f') net /\ (g has_vector_derivative g') net
        ==> ((\x. pastecart (f x) (g x)) has_vector_derivative pastecart f' g')
            net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_PASTECART) THEN
  REWRITE_TAC[PASTECART_CMUL]);;

(* The chart state (position, chart velocity) of a geodesic solves the      *)
(* spray equation.                                                           *)

let GEOL_GEODESIC_CHART_STATE = prove
 (`!atlas (g:A->real^N^N) (gamma:real->A) (c:(A->bool)#(A->real^N)) v t.
        ((\s. SND c (gamma(drop s))) has_vector_derivative v t) (at (lift t)) /\
        ((\s. v(drop s)) has_vector_derivative
         --(christoffel (metric_local atlas c g) (SND c (gamma t)) (v t) (v t)))
        (at (lift t))
        ==> ((\s. pastecart (SND c (gamma(drop s))) (v(drop s)))
             has_vector_derivative
             geo_spray (metric_local atlas c g)
                       (pastecart (SND c (gamma t)) (v t))) (at (lift t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[geo_spray; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MATCH_MP_TAC GEOL_HAS_VECTOR_DERIVATIVE_PASTECART THEN ASM_REWRITE_TAC[]);;

(* Local uniqueness: two geodesics through the same point with the same     *)
(* velocity agree near that time.                                           *)

let GEOL_GEODESIC_LOCAL_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (gamma1:real->A) gamma2 J1 J2 t1.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma1 J1 /\
        mfd_geodesic (top,atlas) g gamma2 J2 /\
        t1 IN J1 /\ t1 IN J2 /\ gamma1 t1 = gamma2 t1 /\
        mfd_vel atlas gamma1 t1 = mfd_vel atlas gamma2 t1
        ==> ?d. &0 < d /\
                !t. abs(t - t1) < d ==> t IN J1 /\ t IN J2 /\ gamma1 t = gamma2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mfd_geodesic]) THEN
  SUBGOAL_THEN `(gamma1:real->A) t1 IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY]; ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) t1)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN atlas /\ (gamma1:real->A) t1 IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the chart velocities *)
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `c:(A->bool)#(A->real^N)`))) o
    check (fun th -> can (term_match []
      `is_realinterval J2 /\ real_open J2 /\
       continuous_map (subtopology euclideanreal J2,top:A topology) gamma2 /\
       (!c:(A->bool)#(A->real^N). c IN atlas ==> P c)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v2:real->real^N`) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `c:(A->bool)#(A->real^N)`))) o
    check (fun th -> can (term_match []
      `is_realinterval J1 /\ real_open J1 /\
       continuous_map (subtopology euclideanreal J1,top:A topology) gamma1 /\
       (!c:(A->bool)#(A->real^N). c IN atlas ==> P c)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v1:real->real^N`) THEN
  (* the chart velocities at t1 agree *)
  SUBGOAL_THEN `(v1:real->real^N) t1 = v2 t1` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `mfd_vel atlas (gamma1:real->A) t1 = (v1:real->real^N) t1 /\
      mfd_vel atlas (gamma2:real->A) t1 = (v2:real->real^N) t1`
     (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[mfd_vel] THEN
    SUBGOAL_THEN `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma2:real->A) t1) = c`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* a common time neighbourhood inside the chart *)
  MP_TAC(ISPECL [`top:A topology`; `gamma1:real->A`; `J1:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `t1:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma2:real->A`; `J2:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `t1:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN
   `!t. abs(t - t1) < min d1 d2
        ==> t IN J1 /\ t IN J2 /\ (gamma1:real->A) t IN FST c /\
            (gamma2:real->A) t IN FST (c:(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* ODE uniqueness for the chart states *)
  ABBREV_TAC `U = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)` THEN
  ABBREV_TAC `X = geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
  SUBGOAL_THEN
   `open (U:real^(N,N)finite_sum->bool) /\
    continuously_differentiable 1 U (X:real^(N,N)finite_sum->real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["U"; "X"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`]
        GEOL_SPRAY_SMOOTH) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[riemannian_metric]; SIMP_TAC[smooth_map_on]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(gamma:real->A) (v:real->real^N) J.
       (!t. abs(t - t1) < min d1 d2 ==> t IN J /\ gamma t IN FST c) /\
       (!t. t IN J /\ gamma t IN FST c
            ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t)
                (at (lift t)) /\
                ((\s. v(drop s)) has_vector_derivative
                 --(christoffel (metric_local atlas c g) (SND c (gamma t))
                                (v t) (v t))) (at (lift t)))
       ==> !t. t IN ball(lift t1,min d1 d2)
               ==> pastecart (SND c (gamma(drop t))) (v(drop t)) =
                   ode_vf_flow X U (t - lift t1)
                     (pastecart (SND c (gamma t1)) (v t1))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`X:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                   `U:real^(N,N)finite_sum->bool`; `ball(lift t1,min d1 d2)`;
                   `\s. pastecart (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))
                                  ((v:real->real^N)(drop s))`; `lift t1`]
      ODE_VF_UNIQUE) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_MIN; LIFT_DROP] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IS_INTERVAL_CONVEX_1; CONVEX_BALL] THEN
      X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `abs(drop s - t1) < min d1 d2` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `drop s IN J /\ (gamma:real->A) (drop s) IN FST (c:(A->bool)#(A->real^N))`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "U" THEN REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN EXPAND_TAC "X" THEN
        MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                       `gamma:real->A`; `c:(A->bool)#(A->real^N)`;
                       `v:real->real^N`; `drop s`] GEOL_GEODESIC_CHART_STATE) THEN
        ASM_SIMP_TAC[LIFT_DROP]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `lift t IN ball(lift t1,min d1 d2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; DIST_LIFT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`gamma1:real->A`; `v1:real->real^N`; `J1:real->bool`]
    (ASSUME `!(gamma:real->A) (v:real->real^N) J.
       (!t. abs(t - t1) < min d1 d2 ==> t IN J /\ gamma t IN FST c) /\
       (!t. t IN J /\ gamma t IN FST c
            ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t)
                (at (lift t)) /\
                ((\s. v(drop s)) has_vector_derivative
                 --(christoffel (metric_local atlas c g) (SND c (gamma t))
                                (v t) (v t))) (at (lift t)))
       ==> !t. t IN ball(lift t1,min d1 d2)
               ==> pastecart (SND c (gamma(drop t))) (v(drop t)) =
                   ode_vf_flow X U (t - lift t1)
                     (pastecart (SND c (gamma t1)) (v t1))`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`gamma2:real->A`; `v2:real->real^N`; `J2:real->bool`]
    (ASSUME `!(gamma:real->A) (v:real->real^N) J.
       (!t. abs(t - t1) < min d1 d2 ==> t IN J /\ gamma t IN FST c) /\
       (!t. t IN J /\ gamma t IN FST c
            ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t)
                (at (lift t)) /\
                ((\s. v(drop s)) has_vector_derivative
                 --(christoffel (metric_local atlas c g) (SND c (gamma t))
                                (v t) (v t))) (at (lift t)))
       ==> !t. t IN ball(lift t1,min d1 d2)
               ==> pastecart (SND c (gamma(drop t))) (v(drop t)) =
                   ode_vf_flow X U (t - lift t1)
                     (pastecart (SND c (gamma t1)) (v t1))`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t`) THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `pastecart (SND (c:(A->bool)#(A->real^N)) ((gamma1:real->A) t))
              ((v1:real->real^N) t) =
    pastecart (SND c ((gamma2:real->A) t)) ((v2:real->real^N) t)`
  MP_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[PASTECART_INJ]] THEN
  DISCH_THEN(MP_TAC o AP_TERM `chart_inv (c:(A->bool)#(A->real^N))` o CONJUNCT1) THEN
  ASM_SIMP_TAC[]);;

(* Continuity of a function of real time that has a vector derivative. *)

let GEOL_VEL_CONTINUOUS = prove
 (`!(v:real->real^N) v' z e.
        ((\s. v(drop s)) has_vector_derivative v') (at (lift z)) /\ &0 < e
        ==> ?d. &0 < d /\ !r. abs(r - z) < d ==> dist(v r,v z) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\s. (v:real->real^N)(drop s)) continuous at (lift z)` MP_TAC THENL
   [ASM_MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_AT; differentiable;
                  has_vector_derivative];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift r`) THEN
  ASM_REWRITE_TAC[DIST_LIFT; LIFT_DROP]);;

(* Chart velocities of curves that agree near r agree at r. *)

let GEOL_CHART_VEL_LOCAL_EQ = prove
 (`!(gamma1:real->A) gamma2 (phi:A->real^N) v1 v2 r d.
        &0 < d /\ (!s. abs(s - r) < d ==> gamma1 s = gamma2 s) /\
        ((\s. phi(gamma1(drop s))) has_vector_derivative v1) (at (lift r)) /\
        ((\s. phi(gamma2(drop s))) has_vector_derivative v2) (at (lift r))
        ==> v1 = v2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. (phi:A->real^N)((gamma2:real->A)(drop s))` THEN
  EXISTS_TAC `lift r` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
  EXISTS_TAC `\s. (phi:A->real^N)((gamma1:real->A)(drop s))` THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Unpacking geodesics. *)

let GEOL_GEODESIC_CHART_VEL_EXISTS = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c.
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas
        ==> ?v. !t. t IN J /\ gamma t IN FST c
                    ==> ((\s. SND c (gamma(drop s))) has_vector_derivative v t)
                        (at (lift t)) /\
                        ((\s. v(drop s)) has_vector_derivative
                         --(christoffel (metric_local atlas c g) (SND c (gamma t))
                                        (v t) (v t))) (at (lift t))`,
  REWRITE_TAC[mfd_geodesic] THEN MESON_TAC[]);;

let GEOL_GEODESIC_BASIC = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J.
        mfd_geodesic (top,atlas) g gamma J
        ==> is_realinterval J /\ real_open J /\
            continuous_map (subtopology euclideanreal J,top) gamma`,
  SIMP_TAC[mfd_geodesic]);;

(* Geodesics take values in the space. *)

let GEOL_GEODESIC_IN_TOPSPACE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J t.
        mfd_geodesic (top,atlas) g gamma J /\ t IN J ==> gamma t IN topspace top`,
  REWRITE_TAC[mfd_geodesic; continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

(* The set of times near which two geodesics agree has open complement. *)

let GEOL_UNIQUE_COMPLEMENT = prove
 (`!top atlas (g:A->real^N^N) (gamma1:real->A) gamma2 J1 J2 z.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma1 J1 /\
        mfd_geodesic (top,atlas) g gamma2 J2 /\
        z IN J1 /\ z IN J2 /\
        ~(?d. &0 < d /\
              !s. abs(s - z) < d ==> s IN J1 /\ s IN J2 /\ gamma1 s = gamma2 s)
        ==> ?d. &0 < d /\
                !s. abs(s - z) < d
                    ==> s IN J1 /\ s IN J2 /\
                        ~(?d'. &0 < d' /\
                               !r. abs(r - s) < d'
                                   ==> r IN J1 /\ r IN J2 /\ gamma1 r = gamma2 r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma1:real->A`; `J1:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma2:real->A`; `J2:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma1:real->A) z IN topspace top /\ (gamma2:real->A) z IN topspace top`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`] THENL
     [EXISTS_TAC `J1:real->bool`; EXISTS_TAC `J2:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(gamma1:real->A) z = gamma2 z` THENL
   [ALL_TAC;
    FIRST_ASSUM(MP_TAC o SPECL [`(gamma1:real->A) z`; `(gamma2:real->A) z`] o
      GEN_REWRITE_RULE I [hausdorff_space]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u1:A->bool`; `u2:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma1:real->A`; `J1:real->bool`;
                   `u1:A->bool`; `z:real`] GEOL_CURVE_NEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma2:real->A`; `J2:real->bool`;
                   `u2:A->bool`; `z:real`] GEOL_CURVE_NEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `s IN J1 /\ (gamma1:real->A) s IN u1 /\ s IN J2 /\ (gamma2:real->A) s IN u2`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d':real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN ASM SET_TAC[]] THEN
  (* equal points: the velocities differ *)
  SUBGOAL_THEN
   `~(mfd_vel (atlas:((A->bool)#(A->real^N))->bool) (gamma1:real->A) z =
      mfd_vel atlas gamma2 z)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(?d. &0 < d /\
            !s. abs(s - z) < d ==> s IN J1 /\ s IN J2 /\
                                   (gamma1:real->A) s = gamma2 s)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_LOCAL_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma1:real->A) z)` THEN
  SUBGOAL_THEN `(c:(A->bool)#(A->real^N)) IN atlas /\ (gamma1:real->A) z IN FST c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma1:real->A`; `J1:real->bool`;
                 `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v1:real->real^N`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma2:real->A`; `J2:real->bool`;
                 `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v2:real->real^N`) THEN
  SUBGOAL_THEN `~((v1:real->real^N) z = v2 z)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `mfd_vel atlas (gamma1:real->A) z = (v1:real->real^N) z /\
      mfd_vel atlas (gamma2:real->A) z = (v2:real->real^N) z`
     (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[mfd_vel] THEN
    SUBGOAL_THEN
     `chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma2:real->A) z) = c`
    SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
    CONJ_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v1:real->real^N`;
    `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    (SND c ((gamma1:real->A) z)) ((v1:real->real^N) z) (v1 z))`;
    `z:real`; `dist((v1:real->real^N) z,v2 z) / &2`] GEOL_VEL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[REAL_HALF; DIST_POS_LT]];
    DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`v2:real->real^N`;
    `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                    (SND c ((gamma2:real->A) z)) ((v2:real->real^N) z) (v2 z))`;
    `z:real`; `dist((v1:real->real^N) z,v2 z) / &2`] GEOL_VEL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[REAL_HALF; DIST_POS_LT]];
    DISCH_THEN(X_CHOOSE_THEN `d4:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma1:real->A`; `J1:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `z:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `gamma2:real->A`; `J2:real->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `z:real`] GEOL_CURVE_NEAR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (min d1 d2) (min d3 d4)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `s IN J1 /\ (gamma1:real->A) s IN FST c /\
    s IN J2 /\ (gamma2:real->A) s IN FST (c:(A->bool)#(A->real^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d':real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v1:real->real^N) s = v2 s` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_CHART_VEL_LOCAL_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`gamma1:real->A`; `gamma2:real->A`; `SND (c:(A->bool)#(A->real^N))`;
      `s:real`; `d':real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dist((v1:real->real^N) s,v1 z) < dist(v1 z,v2 z) / &2 /\
    dist((v2:real->real^N) s,v2 z) < dist(v1 z,v2 z) / &2`
  MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH]);;

let GEOL_OPEN_IN_REAL_BALL = prove
 (`!J z d. open_in (subtopology euclideanreal J) {s | s IN J /\ abs(s - z) < d}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  EXISTS_TAC `real_interval(z - d,z + d)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN ASM_CASES_TAC `(x:real) IN J` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Uniqueness of geodesics (Hausdorff manifolds). *)

let MFD_GEODESIC_UNIQUE = prove
 (`!top atlas (g:A->real^N^N) (gamma1:real->A) gamma2 J1 J2 t0.
        hausdorff_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma1 J1 /\
        mfd_geodesic (top,atlas) g gamma2 J2 /\
        t0 IN J1 /\ t0 IN J2 /\ gamma1 t0 = gamma2 t0 /\
        mfd_vel atlas gamma1 t0 = mfd_vel atlas gamma2 t0
        ==> !t. t IN J1 INTER J2 ==> gamma1 t = gamma2 t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma1:real->A`; `J1:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma2:real->A`; `J2:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `S = {t | t IN J1 INTER J2 /\
             ?d. &0 < d /\
                 !s. abs(s - t) < d
                     ==> s IN J1 /\ s IN J2 /\ (gamma1:real->A) s = gamma2 s}` THEN
  SUBGOAL_THEN `S = topspace (subtopology euclideanreal (J1 INTER J2))` MP_TAC THENL
   [MATCH_MP_TAC TOPC_CONNECTED_SPACE_CLOPEN THEN EXISTS_TAC `t0:real` THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL] THEN
      ASM_SIMP_TAC[IS_REALINTERVAL_INTER];
      EXPAND_TAC "S" THEN SET_TAC[];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GEOL_GEODESIC_LOCAL_UNIQUE THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `{s | s IN J1 INTER J2 /\ abs(s - z) < d}` THEN
      REWRITE_TAC[GEOL_OPEN_IN_REAL_BALL] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; REAL_SUB_REFL; REAL_ABS_0] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `d - abs(s - z)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `z:real` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma1:real->A`; `gamma2:real->A`;
                     `J1:real->bool`; `J2:real->bool`; `z:real`]
        GEOL_UNIQUE_COMPLEMENT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `{s | s IN J1 INTER J2 /\ abs(s - z) < d}` THEN
      REWRITE_TAC[GEOL_OPEN_IN_REAL_BALL] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; REAL_SUB_REFL; REAL_ABS_0] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER; IN_DIFF] THEN
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    EXPAND_TAC "S" THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_0]]);;

(* ========================================================================= *)
(* Geodesics in a chart are spray flows (MFD_GEODESIC_SPRAY);                *)
(* chart representations are smooth (MFD_GEODESIC_SMOOTH).                  *)
(* ========================================================================= *)

(* The chart velocity of a geodesic is the chart image of mfd_vel. *)

let GEOL_CHART_VEL_EQ = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c v t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas /\
        t IN J /\ gamma t IN FST c /\
        ((\s. SND c (gamma(drop s))) has_vector_derivative v) (at (lift t))
        ==> v = chart_jac (chart_at atlas (gamma t)) c (gamma t)
                          (mfd_vel atlas gamma t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\s. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s))` THEN
  EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_GEODESIC_VEL_CHART THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
  ASM_REWRITE_TAC[]);;

let MFD_GEODESIC_SPRAY = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c t0 t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas /\
        t0 IN J /\ t IN J /\
        (!s. s IN real_interval[min t0 t,max t0 t] ==> gamma s IN FST c)
        ==> lift(t - t0) IN
            ode_vf_maxint (geo_spray (metric_local atlas c g))
              (IMAGE (SND c) (FST c) PCROSS (:real^N))
              (pastecart (SND c (gamma t0))
                         (chart_jac (chart_at atlas (gamma t0)) c (gamma t0)
                                    (mfd_vel atlas gamma t0))) /\
            ode_vf_flow (geo_spray (metric_local atlas c g))
              (IMAGE (SND c) (FST c) PCROSS (:real^N)) (lift(t - t0))
              (pastecart (SND c (gamma t0))
                         (chart_jac (chart_at atlas (gamma t0)) c (gamma t0)
                                    (mfd_vel atlas gamma t0))) =
            pastecart (SND c (gamma t))
                      (chart_jac (chart_at atlas (gamma t)) c (gamma t)
                                 (mfd_vel atlas gamma t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                 `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real->real^N`) THEN
  SUBGOAL_THEN `real_interval[min t0 t,max t0 t] SUBSET J` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [is_realinterval] o
      check (fun th -> can (term_match [] `is_realinterval (J:real->bool)`)
                         (concl th))) THEN
    ASM_CASES_TAC `t0 <= t` THENL
     [MAP_EVERY EXISTS_TAC [`t0:real`; `t:real`];
      MAP_EVERY EXISTS_TAC [`t:real`; `t0:real`]] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN real_interval[min t0 t,max t0 t]
        ==> (v:real->real^N) s =
            chart_jac (chart_at atlas ((gamma:real->A) s)) c (gamma s)
                      (mfd_vel atlas gamma s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GEOL_CHART_VEL_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 IN real_interval[min t0 t,max t0 t] /\
                t IN real_interval[min t0 t,max t0 t]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))`;
    `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)`;
    `interval[lift(min t0 t),lift(max t0 t)]`;
    `\s. pastecart (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(drop s)))
                   ((v:real->real^N)(drop s))`; `lift t0`] ODE_VF_UNIQUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN REWRITE_TAC[OPEN_UNIV] THEN
      ASM_MESON_TAC[MFDM_CHART];
      MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                     `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`]
        GEOL_SPRAY_SMOOTH) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[riemannian_metric]; SIMP_TAC[smooth_map_on]];
      REWRITE_TAC[IS_INTERVAL_INTERVAL];
      REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL; FORALL_IN_IMAGE; LIFT_DROP] THEN
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `s IN J /\ (gamma:real->A) s IN FST (c:(A->bool)#(A->real^N))`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
        MATCH_MP_TAC GEOL_GEODESIC_CHART_STATE THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift t`) THEN
  REWRITE_TAC[GSYM IMAGE_LIFT_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; LIFT_DROP; GSYM LIFT_SUB]);;

(* Chart representations of geodesics are smooth (locally the first        *)
(* component of the spray flow, which is smooth in time).                   *)

let MFD_GEODESIC_SMOOTH = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas
        ==> open {lift t | t IN J /\ gamma t IN FST c} /\
            smooth_map_on {lift t | t IN J /\ gamma t IN FST c}
                          (\s. SND c (gamma(drop s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_open {t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_CURVE_OPEN_TIMES THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{lift t | t IN J /\ (gamma:real->A) t IN FST c} =
    IMAGE lift {t | t IN J /\ gamma t IN FST (c:(A->bool)#(A->real^N))}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open (IMAGE lift {t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))})`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[GSYM REAL_OPEN]; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `t0:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0:real` o GEN_REWRITE_RULE I [real_open] o
    check (fun th -> can (term_match []
      `real_open {t | t IN J /\ (gamma:real->A) t IN FST (c:(A->bool)#(A->real^N))}`)
      (concl th))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `X = geo_spray (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))` THEN
  ABBREV_TAC `D = IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c) PCROSS (:real^N)` THEN
  ABBREV_TAC
   `z0 = pastecart (SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t0))
                   (chart_jac (chart_at atlas (gamma t0)) c (gamma t0)
                              (mfd_vel atlas gamma t0))` THEN
  (* along the segment from t0 the chart state is the flow *)
  SUBGOAL_THEN
   `!t. abs(t - t0) < d
        ==> lift(t - t0) IN ode_vf_maxint (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                          D z0 /\
            SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t) =
            fstcart(ode_vf_flow X D (lift(t - t0)) z0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`; `t0:real`; `t:real`]
      MFD_GEODESIC_SPRAY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real` o check (fun th -> can (term_match []
        `!x'. abs(x' - t0) < d ==> x' IN J /\ (gamma:real->A) x' IN FST (c:(A->bool)#(A->real^N))`)
        (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      SIMP_TAC[FSTCART_PASTECART]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^(N,N)finite_sum) IN D` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["z0"; "D"] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (D:real^(N,N)finite_sum->bool) /\
    smooth_map_on D (X:real^(N,N)finite_sum->real^(N,N)finite_sum)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "X"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC GEOL_SPRAY_SMOOTH THEN ASM_MESON_TAC[riemannian_metric]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^(N,N)finite_sum->real^(N,N)finite_sum`;
                 `D:real^(N,N)finite_sum->bool`] ODE_VF_FLOW_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `ball(lift t0,d)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `fstcart o (\w. ode_vf_flow (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D
                               (fstcart w) (sndcart w)) o
    (\s:real^1. pastecart (s - lift t0) (z0:real^(N,N)finite_sum))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_TAC THEN REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th -> can (term_match []
      `!t. abs(t - t0) < d
           ==> lift(t - t0) IN ode_vf_maxint (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                              D z0 /\
               SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t) =
               fstcart(ode_vf_flow X D (lift(t - t0)) z0)`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[LIFT_SUB; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN REWRITE_TAC[OPEN_BALL; LINEAR_FSTCART] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `ode_vf_domain (X:real^(N,N)finite_sum->real^(N,N)finite_sum) D` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[ode_vf_domain; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`s - lift t0`; `z0:real^(N,N)finite_sum`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s` o check (fun th -> can (term_match []
      `!t. abs(t - t0) < d
           ==> lift(t - t0) IN ode_vf_maxint (X:real^(N,N)finite_sum->real^(N,N)finite_sum)
                                              D z0 /\
               SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) t) =
               fstcart(ode_vf_flow X D (lift(t - t0)) z0)`) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[LIFT_SUB; LIFT_DROP]];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; SMOOTH_MAP_ON_ID]]);;

(* ========================================================================= *)
(* Geodesics have constant speed (MFD_GEODESIC_SPEED).                       *)
(* ========================================================================= *)

(* The energy v.(g v) computed in any chart containing gamma t. *)

let GEOL_ENERGY_CHART = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J c v t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ c IN atlas /\
        t IN J /\ gamma t IN FST c /\
        ((\s. SND c (gamma(drop s))) has_vector_derivative v) (at (lift t))
        ==> mfd_vel atlas gamma t dot (g(gamma t) ** mfd_vel atlas gamma t) =
            v dot (metric_local atlas c g (SND c (gamma t)) ** v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t IN topspace top` ASSUME_TAC THENL
   [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
    MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                          `J:real->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(gamma:real->A) t`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) t)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(v:real^N) = chart_jac (c0:(A->bool)#(A->real^N)) c ((gamma:real->A) t)
                          (mfd_vel atlas gamma t)`
  SUBST1_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC GEOL_CHART_VEL_EQ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `g:A->real^N^N`; `J:real->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `g:A->real^N^N`; `(gamma:real->A) t`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `(gamma:real->A) t`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`chart_jac (c:(A->bool)#(A->real^N)) c0 ((gamma:real->A) t)`;
                 `(g:A->real^N^N)((gamma:real->A) t)`;
                 `chart_jac (c0:(A->bool)#(A->real^N)) c ((gamma:real->A) t)
                            (mfd_vel atlas gamma t)`] GRGD_QUAD_CONGR) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                   `(gamma:real->A) t`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c0:(A->bool)#(A->real^N))`; `SND(c0:(A->bool)#(A->real^N))`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `(gamma:real->A) t`] CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* Along a solution of the geodesic equation for a metric field G, the     *)
(* energy v.(G(y) v) has zero derivative.                                   *)

let GEOL_ENERGY_DERIV_ZERO = prove
 (`!U (G:real^N->real^N^N) (y:real->real^N) (v:real->real^N) t.
        metric_field U G /\ y t IN U /\
        ((\s. y(drop s)) has_vector_derivative v t) (at (lift t)) /\
        ((\s. v(drop s)) has_vector_derivative
         --(christoffel G (y t) (v t) (v t))) (at (lift t))
        ==> ((\s. lift(v(drop s) dot (G(y(drop s)) ** v(drop s))))
             has_vector_derivative vec 0) (at (lift t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((vectorize:real^N^N->real^(N,N)finite_prod) o G)
                differentiable at ((y:real->real^N) t)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_MESON_TAC[metric_field];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. (G:real^N->real^N^N)((y:real->real^N)(drop s))`;
    `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
       (at ((y:real->real^N) t)) o (\h:real^1. drop h % (v:real->real^N) t)`;
    `\s. (v:real->real^N)(drop s)`;
    `\h:real^1. drop h % --(christoffel (G:real^N->real^N^N) ((y:real->real^N) t)
                                        ((v:real->real^N) t) (v t))`;
    `\s. (v:real->real^N)(drop s)`;
    `\h:real^1. drop h % --(christoffel (G:real^N->real^N^N) ((y:real->real^N) t)
                                        ((v:real->real^N) t) (v t))`;
    `lift t`] LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[has_vector_derivative]) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\s. (G:real^N->real^N^N)((y:real->real^N)(drop s))) =
      (vectorize o G) o (\s. y(drop s))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; has_vector_derivative; VECTOR_MUL_RZERO] THEN
  MATCH_MP_TAC(MESON[]
   `(f':real^1->real^1) = f''
    ==> ((f:real^1->real^1) has_derivative f') (net:(real^1)net)
        ==> (f has_derivative f'') net`) THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `h:real^1` THEN
  ONCE_REWRITE_TAC[GSYM LIFT_NUM] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(matrify:real^(N,N)finite_prod->real^N^N)
      (frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o G)
         (at ((y:real->real^N) t)) (drop h % (v:real->real^N) t)) =
    drop h %% mderiv G (y t) (v t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM mderiv] THEN ASM_MESON_TAC[LRG_MDERIV_LINEAR];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real->real^N) t`;
                 `(v:real->real^N) t`; `(v:real->real^N) t`; `(v:real->real^N) t`]
    LRG_MDERIV_CHRISTOFFEL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `(y:real->real^N) t`;
                 `christoffel (G:real^N->real^N^N) ((y:real->real^N) t)
                    ((v:real->real^N) t) (v t)`;
                 `(v:real->real^N) t`] LRG_METRIC_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL;
              DOT_LNEG; DOT_RNEG; MATRIX_VECTOR_MUL_RNEG; DOT_RADD] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC);;

let MFD_GEODESIC_SPEED = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J s t.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J /\ s IN J /\ t IN J
        ==> mfd_tnorm g (gamma s) (mfd_vel atlas gamma s) =
            mfd_tnorm g (gamma t) (mfd_vel atlas gamma t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_tnorm] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\r. mfd_vel atlas (gamma:real->A) r dot
         ((g:A->real^N^N)(gamma r) ** mfd_vel atlas gamma r)`;
    `J:real->bool`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT; LIFT_NUM] THEN
    SUBGOAL_THEN `(gamma:real->A) r IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A) r`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) ((gamma:real->A) r)` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real->real^N`) THEN
    MP_TAC(ISPECL [`top:A topology`; `gamma:real->A`; `J:real->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `r:real`] GEOL_CURVE_NEAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC
     `\s. lift((v:real->real^N)(drop s) dot
               (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)
                  (SND c ((gamma:real->A)(drop s))) ** v(drop s)))` THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^1` THEN REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC GEOL_ENERGY_CHART THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `J:real->bool`] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC GEOL_ENERGY_DERIV_ZERO THEN
      EXISTS_TAC `IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM_MESON_TAC[riemannian_metric]];
    REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Affine reparametrization (MFD_GEODESIC_AFFINE).                           *)
(* ========================================================================= *)

(* Chain rule for an affine change of real time. *)

let GEOL_AFFINE_CHAIN = prove
 (`!(f:real->real^N) f' a b t.
        ((\s. f(drop s)) has_vector_derivative f') (at (lift(a * t + b)))
        ==> ((\s. f(a * drop s + b)) has_vector_derivative (a % f'))
            (at (lift t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:real^1. lift(a * drop s + b)`; `\s. (f:real->real^N)(drop s)`;
                 `lift a`; `f':real^N`; `lift t`] VECTOR_DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\s:real^1. lift(a * drop s + b)) = (\s. a % s + lift b)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; LIFT_ADD; LIFT_CMUL; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `lift a = a % vec 1 + vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_RID; GSYM LIFT_EQ_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_ID]);;

(* The time set of an affine reparametrization of an open interval. *)

let GEOL_AFFINE_TIMES = prove
 (`!J a b. is_realinterval J /\ real_open J
           ==> is_realinterval {t | a * t + b IN J} /\
               real_open {t | a * t + b IN J}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_realinterval; real_open; IN_ELIM_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t1:real`; `t2:real`; `t:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= a` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a * t1 + b`; `a * t2 + b`; `a * t + b`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`a * t2 + b`; `a * t1 + b`; `a * t + b`])] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LE_RADD] THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC) THEN
    ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a * t + b`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / (abs a + &1)` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < abs a + &1`] THEN
    X_GEN_TAC `t':real` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(a * t' + b) - (a * t + b) = a * (t' - t)`] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(t' - t) * (abs a + &1) < e` MP_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs a + &1`]; ALL_TAC] THEN
    MP_TAC(SPEC `t' - t` REAL_ABS_POS) THEN REAL_ARITH_TAC]);;

let MFD_GEODESIC_AFFINE = prove
 (`!top atlas (g:A->real^N^N) (gamma:real->A) J a b.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        mfd_geodesic (top,atlas) g gamma J
        ==> mfd_geodesic (top,atlas) g (\t. gamma(a * t + b))
                         {t | a * t + b IN J} /\
            !t. a * t + b IN J
                ==> mfd_vel atlas (\t. gamma(a * t + b)) t =
                    a % mfd_vel atlas gamma (a * t + b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`]
    GEOL_GEODESIC_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real->bool`; `a:real`; `b:real`] GEOL_AFFINE_TIMES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[mfd_geodesic] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\t. (gamma:real->A)(a * t + b)) = gamma o (\t. a * t + b)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal J` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
        REWRITE_TAC[CONTINUOUS_MAP_ID];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                    IN_ELIM_THM] THEN SIMP_TAC[]];
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                     `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real->real^N`) THEN
      EXISTS_TAC `\t. a % (v:real->real^N)(a * t + b)` THEN
      X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a * t + b`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) r)`;
                       `(v:real->real^N)(a * t + b)`; `a:real`; `b:real`; `t:real`]
          GEOL_AFFINE_CHAIN) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`v:real->real^N`;
                       `--(christoffel (metric_local atlas (c:(A->bool)#(A->real^N))
                                          (g:A->real^N^N))
                             (SND c ((gamma:real->A)(a * t + b)))
                             ((v:real->real^N)(a * t + b)) (v(a * t + b)))`;
                       `a:real`; `b:real`; `t:real`] GEOL_AFFINE_CHAIN) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o BETA_RULE o SPEC `a:real` o
                   MATCH_MP HAS_VECTOR_DERIVATIVE_CMUL) THEN
        MATCH_MP_TAC(MESON[]
         `(a:real^N) = b ==> (f has_vector_derivative a) (net:(real^1)net)
                             ==> (f has_vector_derivative b) net`) THEN
        MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)`;
                       `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                       `SND (c:(A->bool)#(A->real^N)) ((gamma:real->A)(a * t + b))`]
          CHRISTOFFEL_BILINEAR) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SIMP_TAC[BILINEAR_LMUL; BILINEAR_RMUL] THEN DISCH_TAC THEN
        VECTOR_ARITH_TAC]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(gamma:real->A)(a * t + b) IN topspace top` ASSUME_TAC THENL
     [MATCH_MP_TAC GEOL_GEODESIC_IN_TOPSPACE THEN
      MAP_EVERY EXISTS_TAC [`atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                            `J:real->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(gamma:real->A)(a * t + b)`] CHART_AT) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                             ((gamma:real->A)(a * t + b))` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `gamma:real->A`; `J:real->bool`;
                   `c:(A->bool)#(A->real^N)`] GEOL_GEODESIC_CHART_VEL_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real->real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a * t + b`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `mfd_vel atlas (gamma:real->A) (a * t + b) = (v:real->real^N)(a * t + b)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[mfd_vel] THEN MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[mfd_vel] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
    MP_TAC(ISPECL [`\r. SND (c:(A->bool)#(A->real^N)) ((gamma:real->A) r)`;
                   `(v:real->real^N)(a * t + b)`; `a:real`; `b:real`; `t:real`]
      GEOL_AFFINE_CHAIN) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Teeth tests in flat real^N: geodesics are the affine lines                *)
(* (MFD_GEODESIC_EUCLIDEAN) and exp_x v = x + v (MFD_EXP_EUCLIDEAN).         *)
(* ========================================================================= *)

(* Christoffel symbols of a constant metric vanish (the same fact as         *)
(* LRG_CHRISTOFFEL_CONST of pc_lrg_lap, which this unit does not load).      *)

let GEOL_CHRISTOFFEL_CONST = prove
 (`!(A:real^N^N) z u v. christoffel (\z. A) z u v = vec 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[christoffel; mderiv; o_DEF; FRECHET_DERIVATIVE_CONST_AT;
              MATRIFY_0; MATRIX_VECTOR_MUL_LZERO; DOT_RZERO; VEC_COMPONENT;
              REAL_ADD_LID; REAL_SUB_REFL; REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `(lambda k. &0):real^N = vec 0` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; VEC_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO]);;

(* The flat manifold real^N. *)

let GEOL_EUCLID_FACTS = prove
 (`hausdorff_space (euclidean:(real^N)topology) /\
   smooth_manifold_atlas euclidean (open_set_atlas (:real^N)) /\
   riemannian_metric (open_set_atlas (:real^N)) (\x. mat 1) /\
   (!x:real^N. chart_at (open_set_atlas (:real^N)) x = ((:real^N),(\x. x))) /\
   (!y. metric_local (open_set_atlas (:real^N)) ((:real^N),(\x:real^N. x))
                     (\x. mat 1) y = mat 1)`,
  MP_TAC(ISPEC `(:real^N)` MFD_EUCLIDEAN_OPEN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MFDD_OPEN_SET_CHART_AT THEN REWRITE_TAC[IN_UNIV];
    GEN_TAC THEN
    MP_TAC(ISPECL [`(:real^N)`; `y:real^N`] GRGD_EUCLID_METRIC_LOCAL) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; GSYM open_set_atlas]]);;

let GEOL_LINEAR_DROP_VMUL = prove
 (`!b:real^N. linear (\s:real^1. drop s % b)`,
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC);;

let MFD_GEODESIC_EUCLIDEAN = prove
 (`!gamma:real->real^N.
        mfd_geodesic (euclidean,open_set_atlas (:real^N)) (\x. mat 1) gamma (:real) <=>
        ?a b. !t. gamma t = a + t % b`,
  GEN_TAC THEN REWRITE_TAC[mfd_geodesic; IS_REALINTERVAL_UNIV; REAL_OPEN_UNIV] THEN
  SUBGOAL_THEN
   `!c. c IN open_set_atlas (:real^N) <=> c = ((:real^N),(\x:real^N. x))`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[open_set_atlas; IN_SING]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[GSYM open_set_atlas; IN_UNIV] THEN
  SUBGOAL_THEN
   `metric_local (open_set_atlas (:real^N)) ((:real^N),(\x:real^N. x)) (\x. mat 1) =
    (\y. mat 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; GEOL_EUCLID_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[GEOL_CHRISTOFFEL_CONST; VECTOR_NEG_0] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_TAC `v:real->real^N`)) THEN
    MP_TAC(ISPECL [`\s. (v:real->real^N)(drop s)`; `(:real^1)`]
      HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN ANTS_TAC THENL
     [X_GEN_TAC `s:real^1` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop s`) THEN
      REWRITE_TAC[LIFT_DROP; has_vector_derivative; VECTOR_MUL_RZERO] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
    MP_TAC(ISPECL [`\s. (gamma:real->real^N)(drop s) - drop s % b`; `(:real^1)`]
      HAS_DERIVATIVE_ZERO_CONSTANT) THEN
    REWRITE_TAC[CONVEX_UNIV; IN_UNIV; WITHIN_UNIV] THEN ANTS_TAC THENL
     [X_GEN_TAC `s:real^1` THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `drop s`) THEN
      REWRITE_TAC[LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^1`) THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
      DISCH_THEN(MP_TAC o C CONJ (MP (ISPECL [`\s:real^1. drop s % (b:real^N)`;
                                              `at (s:real^1)`] HAS_DERIVATIVE_LINEAR)
                                       (SPEC `b:real^N` GEOL_LINEAR_DROP_VMUL))) THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_SUB) THEN
      BETA_TAC THEN REWRITE_TAC[VECTOR_SUB_REFL; ETA_AX];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN X_GEN_TAC `t:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `lift t`) THEN REWRITE_TAC[LIFT_DROP] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_TAC `b:real^N`)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_DROP_EQ_GEN; IMAGE_LIFT_UNIV] THEN
      REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[GEOL_LINEAR_DROP_VMUL];
      EXISTS_TAC `\t:real. (b:real^N)` THEN
      REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN X_GEN_TAC `t:real` THEN
      MP_TAC(ISPECL [`\s:real^1. (a:real^N)`; `vec 0:real^N`;
                     `\s:real^1. drop s % (b:real^N)`; `b:real^N`; `at (lift t)`]
        HAS_VECTOR_DERIVATIVE_ADD) THEN
      BETA_TAC THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[GEOL_LINEAR_DROP_VMUL]]]);;

(* Straight lines are geodesics of real^N with the expected initial data. *)

let GEOL_EUCLID_LINE = prove
 (`!x v:real^N.
        mfd_geodesic (euclidean,open_set_atlas (:real^N)) (\x. mat 1)
                     (\t. x + t % v) (:real) /\
        (\t. x + t % v) (&0) = x /\
        mfd_vel (open_set_atlas (:real^N)) (\t. x + t % v) (&0) = v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MFD_GEODESIC_EUCLIDEAN] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x:real^N`; `v:real^N`] THEN REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
  REWRITE_TAC[mfd_vel; GEOL_EUCLID_FACTS] THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN
  MP_TAC(ISPECL [`\s:real^1. (x:real^N)`; `vec 0:real^N`;
                 `\s:real^1. drop s % (v:real^N)`; `v:real^N`; `at (lift(&0))`]
    HAS_VECTOR_DERIVATIVE_ADD) THEN
  BETA_TAC THEN REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST; VECTOR_ADD_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[has_vector_derivative] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[GEOL_LINEAR_DROP_VMUL]);;

let MFD_EXP_EUCLIDEAN = prove
 (`!x v:real^N.
        mfd_exp_dom (euclidean,open_set_atlas (:real^N)) (\x. mat 1) x = (:real^N) /\
        mfd_exp (euclidean,open_set_atlas (:real^N)) (\x. mat 1) x v = x + v`,
  SUBGOAL_THEN
   `!x v:real^N.
        mfd_geo_maxint (euclidean,open_set_atlas (:real^N)) (\x. mat 1) x v =
        (:real)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[mfd_geo_maxint] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC(SET_RULE `(s:real->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `\t. (x:real^N) + t % v` THEN REWRITE_TAC[GEOL_EUCLID_LINE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mfd_exp_dom; mfd_exp; IN_UNIV] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[mfd_geo] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  ABBREV_TAC
   `gamma = @gamma. mfd_geodesic (euclidean,open_set_atlas (:real^N)) (\x. mat 1)
                      gamma (:real) /\
                    gamma (&0) = (x:real^N) /\
                    mfd_vel (open_set_atlas (:real^N)) gamma (&0) = v` THEN
  SUBGOAL_THEN
   `mfd_geodesic (euclidean,open_set_atlas (:real^N)) (\x. mat 1)
                 (gamma:real->real^N) (:real) /\
    gamma (&0) = (x:real^N) /\
    mfd_vel (open_set_atlas (:real^N)) gamma (&0) = v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gamma" THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `\t. (x:real^N) + t % v` THEN REWRITE_TAC[GEOL_EUCLID_LINE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `open_set_atlas (:real^N)`;
                 `\x:real^N. mat 1:real^N^N`; `gamma:real->real^N`;
                 `\t. (x:real^N) + t % v`; `(:real)`; `(:real)`; `&0`]
    MFD_GEODESIC_UNIQUE) THEN
  ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; GEOL_EUCLID_LINE; IN_UNIV; INTER_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[VECTOR_MUL_LID]);;

