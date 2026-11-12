(* ========================================================================= *)
(* Unit pc_s2ent_flow: Hamilton's entropy for ancient 2-d Ricci flows on a  *)
(* parametrized S^2 with R > 0 that are pinched at arbitrarily negative     *)
(* times; the headline is                                                   *)
(*   |- !w:B->bool. P2B_REQ_S2_ENTROPY_STATEMENT w                          *)
(* (pc_p2b_s2entreq).  m = int R is constant, A' = -m, and                  *)
(* E = int R log R - m log(m / A) has E' = int (R - r)^2 - int |grad R|^2/R *)
(* <= 0 (S2E_HAMILTON_INEQ), E >= 0, E <= m log(1 + e) at pinched times,    *)
(* so E = 0 and R is constant.                                              *)
(* ========================================================================= *)

needs "src/pc_s2ent_heat.ml";;
needs "src/pc_p2b_s2entreq.ml";;

prioritize_real();;
type_invention_error := true;;

(* A Ricci flow on (a',b) is a flow from any a in (a',b). *)

let S2E_RF_ON_FROM = prove
 (`!top (atlas:((A->bool)#(A->real^N))->bool) a' a b (g:real->A->real^N^N).
     ricci_flow_on (top,atlas) a' b g /\ a' < a /\ a < b
     ==> ricci_flow_from (top,atlas) a b g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ricci_flow_from] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ricci_flow_on] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `interval(lift a',lift b) PCROSS IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    EXISTS_TAC `a - a':real` THEN
    EXISTS_TAC `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas (c:(A->bool)#(A->real^N))
                       ((g:real->A->real^N^N) (drop(fstcart z))) (sndcart z))` THEN
    REWRITE_TAC[REAL_ARITH `a - (a - a') = a':real`; FSTCART_PASTECART; SNDCART_PASTECART;
                LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]]]);;

(* The time derivative of a family smooth up to time a. *)

let S2E_SFUN_TDER_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (e:real->A->real) t x.
     smooth_manifold_atlas top atlas /\ pde_sfun_from atlas a b e /\
     a < t /\ t < b /\ x IN topspace top
     ==> ((\s. e s x) has_real_derivative rfu_tder a e t x) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `e:real->A->real`; `c:(A->bool)#(A->real^N)`] S2E_SFUN_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `SND (c:(A->bool)#(A->real^N)) (x:A) IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rfu_tder a (e:real->A->real) t x =
                drop(frechet_derivative (FF:real^(1,N)finite_sum->real^1)
                       (at (pastecart (lift t) (SND (c:(A->bool)#(A->real^N)) x)))
                       (pastecart (lift(&1)) (vec 0)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`e:real->A->real`; `c:(A->bool)#(A->real^N)`; `a:real`; `b:real`;
                   `d:real`; `FF:real^(1,N)finite_sum->real^1`; `t:real`;
                   `SND (c:(A->bool)#(A->real^N)) (x:A)`] S2E_SFUN_TDER_CHART) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\s. drop((FF:real^(1,N)finite_sum->real^1)
                         (pastecart (lift s) (SND (c:(A->bool)#(A->real^N)) (x:A))))` THEN
  EXISTS_TAC `min (t - a) (b - t):real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real`; `SND (c:(A->bool)#(A->real^N)) (x:A)`] o
      check (fun th -> is_forall(concl th) && s2e_mentions "drop" th)) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MATCH_MP_TAC GRGT_TIME_DERIVATIVE THEN
    EXISTS_TAC `interval(lift(a - d),lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

(* |Ric|^2 = R^2 / 2 in dimension 2, and dR/dt = Lap R + R^2. *)

let S2E_RICNORM2 = prove
 (`!U (G:real^2->real^2^2) y.
     metric_field U G /\ y IN U ==> ltnorm2 2 G (lric2 G) y = lscalar G y pow 2 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] LRG_METRIC_INV_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:real^2^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`]
                RFA_RICNORM_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`] S2E_EINSTEIN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MP_TAC(ISPECL [`U:real^2->bool`; `G:real^2->real^2^2`; `y:real^2`; `S:real^2^2`]
                RFA_FRAME_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[DIMINDEX_2; SUM_2] THEN
  ASM_SIMP_TAC[ARITH; DIMINDEX_2] THEN REAL_ARITH_TAC);;

let S2E_RF_SCALAR_EVOL2 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) a b (h:real->A->real^2^2) t x.
     ricci_flow_on (top,atlas) a b h /\ a < t /\ t < b /\ x IN topspace top
     ==> ((\s. mfd_scalar atlas (h s) x) has_real_derivative
          rfa_lap atlas (h t) (mfd_scalar atlas (h t)) x + mfd_scalar atlas (h t) x pow 2)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `a:real`; `b:real`;
                 `h:real->A->real^2^2`; `t:real`; `x:A`] RFA_MFD_SCALAR_EVOLUTION) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) net
                                  ==> (f has_real_derivative b) net`) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
                riemannian_metric atlas ((h:real->A->real^2^2) t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(chart_at atlas (x:A)))
                        (FST(chart_at (atlas:((A->bool)#(A->real^2))->bool) x))`;
                 `metric_local atlas (chart_at atlas (x:A)) ((h:real->A->real^2^2) t)`;
                 `SND(chart_at (atlas:((A->bool)#(A->real^2))->bool) (x:A)) x`] S2E_RICNORM2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `riemannian_metric atlas ((h:real->A->real^2^2) t)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mfd_scalar] THEN REAL_ARITH_TAC);;

(* R and R log R along an ancient flow are families smooth up to any time. *)

let S2E_RF_SCALAR_SFUN = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a' a b (h:real->A->real^N^N).
     ricci_flow_on (top,atlas) a' b h /\ a' < a
     ==> pde_sfun_from atlas a b (\t. mfd_scalar atlas (h t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `a - a':real` THEN
  EXISTS_TAC `\z. lift(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                        ((h:real->A->real^N^N) (drop(fstcart z)))
                        (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))` THEN
  REWRITE_TAC[REAL_ARITH `a - (a - a') = a':real`; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a':real`; `b:real`;
                 `h:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                RFA_MFD_SCALAR_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` SUBST1_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
    SET_TAC[];
    SIMP_TAC[]]);;

let S2E_RF_RLOGR_SFUN = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a' a b (h:real->A->real^N^N).
     ricci_flow_on (top,atlas) a' b h /\ a' < a /\
     (!t x. t < b /\ x IN topspace top ==> &0 < mfd_scalar atlas (h t) x)
     ==> pde_sfun_from atlas a b
           (\t x. mfd_scalar atlas (h t) x * log(mfd_scalar atlas (h t) x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pde_sfun_from] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `RR = \z. lift(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                        ((h:real->A->real^N^N) (drop(fstcart z)))
                        (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))` THEN
  EXISTS_TAC `a - a':real` THEN
  EXISTS_TAC `\z. lift(drop((RR:real^(1,N)finite_sum->real^1) z) * log(drop(RR z)))` THEN
  EXPAND_TAC "RR" THEN
  REWRITE_TAC[REAL_ARITH `a - (a - a') = a':real`; FSTCART_PASTECART; SNDCART_PASTECART;
              LIFT_DROP] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FST(c:(A->bool)#(A->real^N)) INTER topspace top = FST c` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a':real`; `b:real`;
                 `h:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
                RFA_MFD_SCALAR_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(interval(lift a',lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N))))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a',lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
                 `\z. lift(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                        ((h:real->A->real^N^N) (drop(fstcart z)))
                        (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))`;
                 `\z. lift(log(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                        ((h:real->A->real^N^N) (drop(fstcart z)))
                        (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z))))`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`interval(lift a',lift b) PCROSS IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
                 `\z. lift(mfd_scalar (atlas:((A->bool)#(A->real^N))->bool)
                        ((h:real->A->real^N^N) (drop(fstcart z)))
                        (chart_inv (c:(A->bool)#(A->real^N)) (sndcart z)))`]
                SMOOTH_MAP_ON_LIFT_LOG) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART;
              SNDCART_PASTECART; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Facts at one time.  The gradient of log f, integration by                 *)
(* parts for log R Lap R, and the entropy E = int R log R - m log(m / A) of  *)
(* a surface with R > 0: E >= 0 with equality only if R is constant, and    *)
(* E <= m log(1 + e) when R(x) <= (1 + e) R(y) for all x, y.               *)
(* ------------------------------------------------------------------------- *)

let S2E_MFD_SMOOTH_LOG = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) f.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\
     (!x. x IN topspace top ==> &0 < f x)
     ==> mfd_smooth atlas (\x. lift(log(f x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_smooth; o_DEF] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND c) (FST (c:(A->bool)#(A->real^N)))`;
                 `\y. lift((f:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`]
                SMOOTH_MAP_ON_LIFT_LOG) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(MATCH_MP OPEN_IN_SUBSET (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* The gradient of log f is grad f / f. *)

let S2E_GINNER_LOG = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f b x.
     smooth_manifold_atlas top atlas /\ mfd_smooth atlas (\x. lift(f x)) /\
     x IN topspace top /\ &0 < f x
     ==> s2e_ginner atlas g (\x. log(f x)) b x = s2e_ginner atlas g f b x / f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[s2e_ginner; rfa_lginner] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!h. rfa_d1 (\y. log((f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) y)))
               (SND(chart_at atlas x) (x:A)) h =
        inv(f x) * rfa_d1 (\y. f(chart_inv (chart_at atlas x) y)) (SND(chart_at atlas x) x) h`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`\y. (f:A->real)(chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) x) y)`;
                   `log`; `inv((f:A->real) x)`;
                   `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`; `h:real^N`]
                  RFA_D1_COMPOSE_AT) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (SND(chart_at atlas (x:A)))
                      (FST(chart_at (atlas:((A->bool)#(A->real^N))->bool) x))` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((f:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REAL_ARITH_TAC);;

(* int (log R Lap R + |grad R|^2 / R) = 0. *)

let S2E_LOG_IBP = prove
 (`!(top:A topology) atlas (g:A->real^N^N) f.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(f x)) /\
     (!x. x IN topspace top ==> &0 < f x)
     ==> mfd_has_integral (top,atlas) g
           (\x. log(f x) * rfa_lap atlas g f x + s2e_ginner atlas g f f x / f x)
           (topspace top) (&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                 `\x:A. log((f:A->real) x)`; `f:A->real`] S2E_IBP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_MFD_SMOOTH_LOG THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC S2E_GINNER_LOG THEN EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[]);;

(* log y < y - 1 for y <> 1, and x log(x / r) >= x - r with equality only   *)
(* at x = r.                                                                 *)

let S2E_LOG_STRICT = prove
 (`!y. &0 < y /\ ~(y = &1) ==> log y < y - &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sqrt y` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `sqrt y - &1` LOG_LE_STRONG) THEN
  REWRITE_TAC[REAL_ARITH `&1 + (s - &1) = s`] THEN ASM_SIMP_TAC[LOG_SQRT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sqrt y pow 2 = y` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sqrt y = &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(y = &1)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `sqrt y pow 2 = y` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (sqrt y - &1) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC ORELSE
    (REWRITE_TAC[REAL_LT_LE; REAL_LE_POW_2] THEN
     REWRITE_TAC[REAL_ARITH `~(&0 = x) <=> ~(x = &0)`; REAL_POW_EQ_0] THEN
     ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  UNDISCH_TAC `sqrt y pow 2 = y` THEN UNDISCH_TAC `log y / &2 <= sqrt y - &1` THEN
  REAL_ARITH_TAC);;

let S2E_XLOGX = prove
 (`!x r. &0 < x /\ &0 < r
         ==> x - r <= x * log(x / r) /\ (x * log(x / r) = x - r ==> x = r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x * log(x / r) = --(x * log(r / x))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / x` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `x * (r / x - &1) = r - x` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `r / x - &1` LOG_LE_STRONG) THEN
    REWRITE_TAC[REAL_ARITH `&1 + (y - &1) = y`] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x * l <= x * (r / x - &1) /\ x * (r / x - &1) = r - x
                             ==> x - r <= --(x * l)`) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(r / x = &1)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(x:real = r)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `r / x = &1` THEN UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MP_TAC(SPEC `r / x` S2E_LOG_STRICT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x * l < x * (r / x - &1) /\ x * (r / x - &1) = r - x
                             ==> ~(--(x * l) = x - r)`) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ]]);;

(* The entropy at one time. *)

let S2E_ENTROPY_STATIC = prove
 (`!(top:A topology) atlas (g:A->real^N^N) R AA m.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     riemannian_metric atlas g /\ mfd_smooth atlas (\x. lift(R x)) /\
     (!x. x IN topspace top ==> &0 < R x) /\ ~(topspace top = {}) /\
     AA = mfd_integral (top,atlas) g (topspace top) (\x. &1) /\
     m = mfd_integral (top,atlas) g (topspace top) R
     ==> &0 < AA /\ &0 < m /\
         &0 <= mfd_integral (top,atlas) g (topspace top) (\x. R x * log(R x)) - m * log(m / AA) /\
         (mfd_integral (top,atlas) g (topspace top) (\x. R x * log(R x)) - m * log(m / AA) = &0
          ==> !x. x IN topspace top ==> R x = m / AA) /\
         (!e. (!x y. x IN topspace top /\ y IN topspace top ==> R x <= (&1 + e) * R y)
              ==> mfd_integral (top,atlas) g (topspace top) (\x. R x * log(R x)) - m * log(m / AA)
                  <= m * log(&1 + e))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:A`) THEN
  SUBGOAL_THEN
   `!h:A->real. mfd_smooth atlas (\x. lift(h x))
                ==> mfd_has_integral (top,atlas) (g:A->real^N^N) h (topspace top)
                                     (mfd_integral (top,atlas) g (topspace top) h)`
  (LABEL_TAC "INT") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
    MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x:A. lift(log((R:A->real) x)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_MFD_SMOOTH_LOG THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `NN = mfd_integral (top,atlas) (g:A->real^N^N) (topspace top)
                     (\x:A. (R:A->real) x * log(R x))` THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:A->real^N^N) (\x:A. &1) (topspace top) AA /\
    mfd_has_integral (top,atlas) g (R:A->real) (topspace top) m /\
    mfd_has_integral (top,atlas) g (\x:A. (R:A->real) x * log(R x)) (topspace top) NN`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "NN" THEN REPEAT CONJ_TAC THEN
    USE_THEN "INT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST] THEN
    MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < AA` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `x0:A`] S2E_INT_ONE_POS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `AA = mfd_integral (top,atlas) (g:A->real^N^N) (topspace top) (\x:A. &1)`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `m = mfd_integral (top,atlas) (g:A->real^N^N) (topspace top) (R:A->real)`)) THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                           `g:A->real^N^N`; `\x:A. &0 * &1`; `R:A->real`;
                           `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_LE] THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `\x:A. &1`; `topspace(top:A topology)`; `AA:real`; `&0`]
                    MFD_HAS_INTEGRAL_CMUL) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `R:A->real`; `x0:A`] RFU_MFD_INTEGRAL_ZERO_IMP) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_IMP_NZ] THEN
    X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((R:A->real) x))` THEN
    REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = m / AA` THEN
  SUBGOAL_THEN `&0 < r /\ r * AA = m` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  (* E is the integral of R log(R / r) and of phi = R log(R / r) - R + r *)
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) (g:A->real^N^N) (\x:A. (R:A->real) x * log(R x / r))
                     (topspace top) (NN - m * log r) /\
    mfd_has_integral (top,atlas) g (\x:A. (R:A->real) x * log(R x / r) - R x + r * &1)
                     (topspace top) (NN - m * log r)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `\x:A. (R:A->real) x * log(R x)`; `\x:A. log r * (R:A->real) x`;
                     `topspace(top:A topology)`; `NN:real`; `log r * m`] MFD_HAS_INTEGRAL_SUB) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN
        ASM_REWRITE_TAC[ETA_AX];
        ALL_TAC] THEN
      SUBGOAL_THEN `NN - log r * m = NN - m * log r` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                     `\x:A. (R:A->real) x * log(R x / r) - R x`; `\x:A. r * &1`;
                     `topspace(top:A topology)`; `(NN - m * log r) - m`; `r * AA`]
                    MFD_HAS_INTEGRAL_ADD) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CMUL] THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `\x:A. (R:A->real) x * log(R x / r)`; `R:A->real`;
                       `topspace(top:A topology)`; `NN - m * log r`; `m:real`]
                      MFD_HAS_INTEGRAL_SUB) THEN
        ASM_REWRITE_TAC[ETA_AX];
        ASM_REWRITE_TAC[REAL_ARITH `(a - m) + m = a`]]];
    ALL_TAC] THEN
  (* phi >= 0 *)
  SUBGOAL_THEN `!x:A. x IN topspace top ==> &0 <= (R:A->real) x * log(R x / r) - R x + r * &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`(R:A->real) x`; `r:real`] S2E_XLOGX) THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `g:A->real^N^N`; `\x:A. &0 * &1`;
                         `\x:A. (R:A->real) x * log(R x / r) - R x + r * &1`;
                         `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `\x:A. &1`; `topspace(top:A topology)`; `AA:real`; `&0`]
                  MFD_HAS_INTEGRAL_CMUL) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `g:A->real^N^N`;
                   `\x:A. (R:A->real) x * log(R x / r) - R x + r * &1`; `x:A`]
                  RFU_MFD_INTEGRAL_ZERO_IMP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `mfd_has_integral (top,atlas) (g:A->real^N^N)
                       (\x:A. (R:A->real) x * log(R x / r) - R x + r * &1)
                       (topspace top) (NN - m * log r)` THEN
        ASM_REWRITE_TAC[];
        X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        SUBGOAL_THEN
         `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool)
            (\x:A. lift((R:A->real) x * log(R x / r) - R x + r * &1))`
        MP_TAC THENL
         [MATCH_MP_TAC S2E_MFD_SMOOTH_ADD THEN EXISTS_TAC `top:A topology` THEN
          ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST] THEN
          MATCH_MP_TAC S2E_MFD_SMOOTH_SUB THEN EXISTS_TAC `top:A topology` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN
          EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC S2E_MFD_SMOOTH_LOG THEN EXISTS_TAC `top:A topology` THEN
          ASM_SIMP_TAC[REAL_LT_DIV] THEN
          REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
          MATCH_MP_TAC S2E_MFD_SMOOTH_CMUL THEN EXISTS_TAC `top:A topology` THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[mfd_smooth; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]]];
      DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
      MP_TAC(ISPECL [`(R:A->real) x`; `r:real`] S2E_XLOGX) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the pinched bound *)
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:A. x IN topspace top ==> (R:A->real) x / r <= &1 + e` ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < &1 + e` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `x:A`] o check (fun th -> is_forall(concl th) &&
        s2e_mentions "real_mul" th && s2e_mentions "real_le" th)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < (R:A->real) x` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SPEC_TAC(`(R:A->real) x`,`z:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `z:real` THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `(R:A->real) x * AA <= (&1 + e) * m` MP_TAC THENL
     [ALL_TAC;
      DISCH_TAC THEN EXPAND_TAC "r" THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ]] THEN
    MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                         `g:A->real^N^N`; `\y:A. (R:A->real) x * &1`;
                         `\y:A. (&1 + e) * (R:A->real) y`;
                         `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      X_GEN_TAC `y:A` THEN DISCH_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`] o check (fun th -> is_forall(concl th) &&
        s2e_mentions "real_mul" th && s2e_mentions "real_le" th)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&1 + e) * m` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `\x:A. (R:A->real) x * log(R x / r)`;
                       `\x:A. log(&1 + e) * (R:A->real) x`;
                       `topspace(top:A topology)`] MFD_HAS_INTEGRAL_LE) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x * a <= x * b ==> x * a <= b * x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[REAL_LT_DIV]]);;

(* ------------------------------------------------------------------------- *)
(* Real-variable helpers and the time derivatives of the area                *)
(* A, the mass m = int R and N = int R log R along a flow on a surface.     *)
(* ------------------------------------------------------------------------- *)

let S2E_DERIV_XLOGX = prove
 (`!f f' t. (f has_real_derivative f') (atreal t) /\ &0 < f t
            ==> ((\s. f s * log(f s)) has_real_derivative f' * (log(f t) + &1)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\s. log((f:real->real) s)) has_real_derivative inv(f t) * f') (atreal t)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. log((f:real->real) s)) = log o f` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real`; `\s. log((f:real->real) s)`;
                 `inv((f:real->real) t) * f'`; `t:real`] HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> (g has_real_derivative a) net
                                  ==> (g has_real_derivative b) net`) THEN
  UNDISCH_TAC `&0 < (f:real->real) t` THEN CONV_TAC REAL_FIELD);;

(* Monotonicity and constancy from the sign of the derivative. *)

let S2E_MONO_FROM_DERIV = prove
 (`!f f' a b t1 t0.
     (!t. a < t /\ t < b ==> (f has_real_derivative f' t) (atreal t)) /\
     (!t. a < t /\ t < b ==> f' t <= &0) /\ a < t1 /\ t1 <= t0 /\ t0 < b
     ==> f t0 <= f t1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t1:real = t0` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `t1:real`; `t0:real`] REAL_MVT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      EXISTS_TAC `(f':real->real) x` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&0:real`)) (concl th))) THEN
    UNDISCH_TAC `x IN real_interval(t1,t0)` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `(f':real->real) x * (t0 - t1) <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --a * b ==> a * b <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

let S2E_CONST_FROM_DERIV = prove
 (`!f a b t1 t0.
     (!t. a < t /\ t < b ==> (f has_real_derivative &0) (atreal t)) /\
     a < t1 /\ t1 <= t0 /\ t0 < b
     ==> f t0 = f t1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC S2E_MONO_FROM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`\t:real. &0`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL [`\t:real. --((f:real->real) t)`; `\t:real. &0`]
                                  S2E_MONO_FROM_DERIV)) THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_NEG_0] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_SIMP_TAC[]]);;

(* The time derivative of an integral along a flow, with its value. *)

let S2E_RF_INT_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N)
    (e:real->A->real) t D.
     hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b g /\
     pde_sfun_from atlas a b e /\ a < t /\ t < b /\
     mfd_has_integral (top,atlas) (g t)
       (\x. rfu_tder a e t x - mfd_scalar atlas (g t) x * e t x) (topspace top) D
     ==> ((\s. mfd_integral (top,atlas) (g s) (topspace top) (e s)) has_real_derivative D)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ a < b /\
                riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_RICCI_FLOW_FROM_METRIC; REAL_LT_IMP_LE; ricci_flow_from; ricci_flow_on];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`; `e:real->A->real`; `rfu_tder a (e:real->A->real)`]
                MFD_INTEGRAL_RF_DERIV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RFU_SFUN_TDER THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC S2E_SFUN_TDER_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                            `b:real`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) net
                                    ==> (f has_real_derivative b) net`) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`;
                   `\x:A. rfu_tder a (e:real->A->real) t x -
                          mfd_scalar atlas ((g:real->A->real^N^N) t) x * e t x`;
                   `topspace(top:A topology)`; `D:real`] MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ASM_SIMP_TAC[]]);;

(* dA/dt = -m. *)

let S2E_RF_AREA_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (h:real->A->real^N^N) t.
     hausdorff_space top /\ compact_space top /\ ricci_flow_from (top,atlas) a b h /\
     a < t /\ t < b
     ==> ((\s. mfd_integral (top,atlas) (h s) (topspace top) (\x. &1)) has_real_derivative
          --(mfd_integral (top,atlas) (h t) (topspace top) (mfd_scalar atlas (h t))))
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\ a < b /\
                riemannian_metric atlas ((h:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_RICCI_FLOW_FROM_METRIC; REAL_LT_IMP_LE; ricci_flow_from; ricci_flow_on];
    ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `h:real->A->real^N^N`; `\s:real x:A. &1`]
                       S2E_RF_INT_DERIV)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC S2E_SFUN_CONST THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. rfu_tder a (\s:real x:A. &1) t x = &0` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RFU_TDER_UNIQUE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(h:real->A->real^N^N) t`; `mfd_scalar atlas ((h:real->A->real^N^N) t)`;
                 `topspace(top:A topology)`;
                 `mfd_integral (top,atlas) ((h:real->A->real^N^N) t) (topspace top)
                    (mfd_scalar atlas (h t))`; `--(&1)`] MFD_HAS_INTEGRAL_CMUL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* dm/dt = 0 in dimension 2. *)

let S2E_RF_MASS_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) a' a b (h:real->A->real^2^2) t.
     hausdorff_space top /\ compact_space top /\ ricci_flow_on (top,atlas) a' b h /\
     a' < a /\ a < t /\ t < b
     ==> ((\s. mfd_integral (top,atlas) (h s) (topspace top) (mfd_scalar atlas (h s)))
          has_real_derivative &0) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas:((A->bool)#(A->real^2))->bool) a b h` ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_RF_ON_FROM THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
                riemannian_metric atlas ((h:real->A->real^2^2) t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_RICCI_FLOW_FROM_METRIC; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                       `a:real`; `b:real`; `h:real->A->real^2^2`;
                       `\s:real. mfd_scalar atlas ((h:real->A->real^2^2) s)`]
                      S2E_RF_INT_DERIV)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC S2E_RF_SCALAR_SFUN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> rfu_tder a (\s:real. mfd_scalar atlas ((h:real->A->real^2^2) s)) t x =
              rfa_lap atlas (h t) (mfd_scalar atlas (h t)) x + mfd_scalar atlas (h t) x pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_TDER_UNIQUE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC S2E_RF_SCALAR_EVOL2 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a':real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `(h:real->A->real^2^2) t`; `mfd_scalar atlas ((h:real->A->real^2^2) t)`]
                S2E_INT_LAP_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_SIMP_TAC[] THEN
  REAL_ARITH_TAC);;

(* dN/dt = int R^2 - int |grad R|^2 / R for N = int R log R, dimension 2. *)

let S2E_RF_NN_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) a' a b (h:real->A->real^2^2) t.
     hausdorff_space top /\ compact_space top /\ ricci_flow_on (top,atlas) a' b h /\
     a' < a /\ a < t /\ t < b /\
     (!t x. t < b /\ x IN topspace top ==> &0 < mfd_scalar atlas (h t) x)
     ==> ((\s. mfd_integral (top,atlas) (h s) (topspace top)
                 (\x. mfd_scalar atlas (h s) x * log(mfd_scalar atlas (h s) x)))
          has_real_derivative
          mfd_integral (top,atlas) (h t) (topspace top) (\x. mfd_scalar atlas (h t) x pow 2) -
          mfd_integral (top,atlas) (h t) (topspace top)
            (\x. s2e_ginner atlas (h t) (mfd_scalar atlas (h t)) (mfd_scalar atlas (h t)) x /
                 mfd_scalar atlas (h t) x)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas:((A->bool)#(A->real^2))->bool) a b h` ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_RF_ON_FROM THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
                riemannian_metric atlas ((h:real->A->real^2^2) t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_RICCI_FLOW_FROM_METRIC; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                       `a:real`; `b:real`; `h:real->A->real^2^2`;
                       `\s:real x:A. mfd_scalar atlas ((h:real->A->real^2^2) s) x *
                                    log(mfd_scalar atlas (h s) x)`]
                      S2E_RF_INT_DERIV)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC S2E_RF_RLOGR_SFUN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a':real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas ((h:real->A->real^2^2) t)` THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x:A. lift((R:A->real) x)) /\
                (!x:A. x IN topspace top ==> &0 < R x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN CONJ_TAC THENL
     [MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN topspace top
          ==> rfu_tder a (\s:real x:A. mfd_scalar atlas ((h:real->A->real^2^2) s) x *
                                      log(mfd_scalar atlas (h s) x)) t x =
              (rfa_lap atlas (h t) (R:A->real) x + R x pow 2) * (log(R x) + &1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFU_TDER_UNIQUE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(ISPECL [`\s. mfd_scalar atlas ((h:real->A->real^2^2) s) (x:A)`;
                   `rfa_lap atlas ((h:real->A->real^2^2) t) (R:A->real) x + R x pow 2`; `t:real`]
                  S2E_DERIV_XLOGX) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [EXPAND_TAC "R" THEN MATCH_MP_TAC S2E_RF_SCALAR_EVOL2 THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a':real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the integrals at time t *)
  SUBGOAL_THEN
   `!f:A->real. mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x. lift(f x))
                ==> mfd_has_integral (top,atlas) ((h:real->A->real^2^2) t) f (topspace top)
                                     (mfd_integral (top,atlas) (h t) (topspace top) f)`
  (LABEL_TAC "INT") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN
    MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `(h:real->A->real^2^2) t`; `R:A->real`] S2E_LOG_IBP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `(h:real->A->real^2^2) t`; `R:A->real`] S2E_INT_LAP_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((h:real->A->real^2^2) t) (\x:A. (R:A->real) x pow 2)
      (topspace top) (mfd_integral (top,atlas) (h t) (topspace top) (\x. R x pow 2)) /\
    mfd_has_integral (top,atlas) (h t)
      (\x:A. s2e_ginner atlas (h t) (R:A->real) R x / R x) (topspace top)
      (mfd_integral (top,atlas) (h t) (topspace top) (\x. s2e_ginner atlas (h t) R R x / R x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "INT" MATCH_MP_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[] THEN MATCH_MP_TAC S2E_MFD_SMOOTH_DIV THEN EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MATCH_MP_TAC S2E_GINNER_SMOOTH THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `P2 = mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top)
                     (\x:A. (R:A->real) x pow 2)` THEN
  ABBREV_TAC `X = mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top)
                    (\x:A. s2e_ginner atlas (h t) (R:A->real) R x / R x)` THEN
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((h:real->A->real^2^2) t)
      (\x:A. ((log((R:A->real) x) * rfa_lap atlas (h t) R x + s2e_ginner atlas (h t) R R x / R x) +
              rfa_lap atlas (h t) R x) + (R x pow 2 - s2e_ginner atlas (h t) R R x / R x))
      (topspace top) ((&0 + &0) + (P2 - X))`
  MP_TAC THENL
   [MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MFD_HAS_INTEGRAL_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (R:A->real) x` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The entropy E = N - m log(m / A) along the flow:                          *)
(* E' = int R^2 - int |grad R|^2 / R - m^2 / A = int (R - r)^2 - int ...     *)
(* <= 0 by Hamilton's inequality; E is nonincreasing and m is constant.     *)
(* ------------------------------------------------------------------------- *)

let S2E_ENT_DERIV_REAL = prove
 (`!NN MM AA dN t.
     (NN has_real_derivative dN) (atreal t) /\ (MM has_real_derivative &0) (atreal t) /\
     (AA has_real_derivative --(MM t)) (atreal t) /\ &0 < AA t /\ &0 < MM t
     ==> ((\s. NN s - MM s * log(MM s / AA s)) has_real_derivative
          dN - MM t pow 2 / AA t) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`MM:real->real`; `&0`; `AA:real->real`; `--((MM:real->real) t)`; `t:real`]
                HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. log((MM:real->real) s / (AA:real->real) s)) has_real_derivative
     inv(MM t / AA t) * ((&0 * AA t - MM t * --MM t) / AA t pow 2)) (atreal t)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\s. log((MM:real->real) s / (AA:real->real) s)) = log o (\s. MM s / AA s)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`MM:real->real`; `&0`; `\s. log((MM:real->real) s / (AA:real->real) s)`;
                 `inv((MM:real->real) t / (AA:real->real) t) *
                  ((&0 * AA t - MM t * --MM t) / AA t pow 2)`; `t:real`]
                HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`NN:real->real`; `dN:real`;
                 `\s. (MM:real->real) s * log(MM s / (AA:real->real) s)`;
                 `(MM:real->real) t *
                  inv(MM t / (AA:real->real) t) * ((&0 * AA t - MM t * --MM t) / AA t pow 2) +
                  &0 * log(MM t / AA t)`; `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[] `a = b ==> (f has_real_derivative a) net
                                  ==> (f has_real_derivative b) net`) THEN
  UNDISCH_TAC `&0 < (AA:real->real) t` THEN UNDISCH_TAC `&0 < (MM:real->real) t` THEN
  CONV_TAC REAL_FIELD);;

(* The entropy is nonincreasing: its derivative is <= 0. *)

let S2E_RF_ENT_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) a' a b (h:real->A->real^2^2) t.
     hausdorff_space top /\ compact_space top /\ connected_space top /\
     ricci_flow_on (top,atlas) a' b h /\ a' < a /\ a < t /\ t < b /\ ~(topspace top = {}) /\
     (!t x. t < b /\ x IN topspace top ==> &0 < mfd_scalar atlas (h t) x)
     ==> ?D. ((\s. mfd_integral (top,atlas) (h s) (topspace top)
                     (\x. mfd_scalar atlas (h s) x * log(mfd_scalar atlas (h s) x)) -
                   mfd_integral (top,atlas) (h s) (topspace top) (mfd_scalar atlas (h s)) *
                   log(mfd_integral (top,atlas) (h s) (topspace top) (mfd_scalar atlas (h s)) /
                       mfd_integral (top,atlas) (h s) (topspace top) (\x. &1)))
              has_real_derivative D) (atreal t) /\ D <= &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_from (top,atlas:((A->bool)#(A->real^2))->bool) a b h` ASSUME_TAC THENL
   [MATCH_MP_TAC S2E_RF_ON_FROM THEN EXISTS_TAC `a':real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
                riemannian_metric atlas ((h:real->A->real^2^2) t)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_RICCI_FLOW_FROM_METRIC; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `R = mfd_scalar atlas ((h:real->A->real^2^2) t)` THEN
  SUBGOAL_THEN `mfd_smooth (atlas:((A->bool)#(A->real^2))->bool) (\x:A. lift((R:A->real) x)) /\
                (!x:A. x IN topspace top ==> &0 < R x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN CONJ_TAC THENL
     [MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `AA = mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top) (\x:A. &1)` THEN
  ABBREV_TAC `MM = mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top) (R:A->real)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `(h:real->A->real^2^2) t`; `R:A->real`; `AA:real`; `MM:real`]
                S2E_ENTROPY_STATIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P2 = mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top)
                     (\x:A. (R:A->real) x pow 2)` THEN
  ABBREV_TAC `X = mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top)
                    (\x:A. s2e_ginner atlas (h t) (R:A->real) R x / R x)` THEN
  EXISTS_TAC `(P2 - X) - MM pow 2 / AA` THEN CONJ_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL
     [`\s. mfd_integral (top,atlas) ((h:real->A->real^2^2) s) (topspace top)
             (\x:A. mfd_scalar atlas (h s) x * log(mfd_scalar atlas (h s) x))`;
      `\s. mfd_integral (top,atlas) ((h:real->A->real^2^2) s) (topspace top)
             (mfd_scalar atlas (h s))`;
      `\s. mfd_integral (top,atlas) ((h:real->A->real^2^2) s) (topspace top) (\x:A. &1)`;
      `P2 - X:real`; `t:real`] S2E_ENT_DERIV_REAL)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `a':real`;
                     `a:real`; `b:real`; `h:real->A->real^2^2`; `t:real`] S2E_RF_NN_DERIV) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC S2E_RF_MASS_DERIV THEN
      MAP_EVERY EXISTS_TAC [`a':real`; `a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`; `a:real`;
                     `b:real`; `h:real->A->real^2^2`; `t:real`] S2E_RF_AREA_DERIV) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* Hamilton's inequality at time t *)
  SUBGOAL_THEN
   `mfd_has_integral (top,atlas) ((h:real->A->real^2^2) t) (\x:A. &1) (topspace top) AA /\
    mfd_has_integral (top,atlas) (h t) (R:A->real) (topspace top) MM /\
    mfd_has_integral (top,atlas) (h t) (\x:A. (R:A->real) x pow 2) (topspace top) P2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["AA"; "MM"; "P2"] THEN REPEAT CONJ_TAC THEN
    REWRITE_TAC[GSYM MFD_INTEGRABLE_INTEGRAL] THEN MATCH_MP_TAC S2E_SMOOTH_INTEGRABLE THEN
    ASM_REWRITE_TAC[S2E_MFD_SMOOTH_CONST; ETA_AX] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC PDM_MFD_SMOOTH_MUL THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = MM / AA` THEN
  SUBGOAL_THEN `r * AA = MM` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                 `(h:real->A->real^2^2) t`; `r:real`] S2E_HAMILTON_INEQ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `(h:real->A->real^2^2) t`; `R:A->real`; `\x:A. r * &1`;
                   `topspace(top:A topology)`; `MM:real`; `r * AA`] MFD_HAS_INTEGRAL_SUB) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_integral (top,atlas) ((h:real->A->real^2^2) t) (topspace top)
      (\x:A. ((R:A->real) x - r) pow 2) = P2 - MM pow 2 / AA`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `(h:real->A->real^2^2) t`; `\x:A. ((R:A->real) x - r) pow 2`;
                   `topspace(top:A topology)`; `P2 - MM pow 2 / AA`] MFD_HAS_INTEGRAL_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SUBGOAL_THEN
     `mfd_has_integral (top,atlas) ((h:real->A->real^2^2) t)
        (\x:A. ((R:A->real) x pow 2 - (&2 * r) * R x) + (r pow 2) * &1)
        (topspace top) ((P2 - (&2 * r) * MM) + (r pow 2) * AA)`
    MP_TAC THENL
     [MATCH_MP_TAC MFD_HAS_INTEGRAL_ADD THEN ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CMUL] THEN
      MATCH_MP_TAC MFD_HAS_INTEGRAL_SUB THEN ASM_SIMP_TAC[MFD_HAS_INTEGRAL_CMUL] THEN
      MATCH_MP_TAC MFD_HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN `(P2 - (&2 * r) * MM) + (r pow 2) * AA = P2 - MM pow 2 / AA` SUBST1_TAC THENL
     [EXPAND_TAC "r" THEN UNDISCH_TAC `&0 < AA` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC MFD_HAS_INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "X" THEN EXPAND_TAC "R" THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* E(t0) <= m log(1 + e) for every e > 0 (pinched times below                *)
(* t0), so E(t0) = 0 and R(t0) is constant; the parametrization by S^2      *)
(* gives compactness and connectedness; the headline                         *)
(*   |- !w:B->bool. P2B_REQ_S2_ENTROPY_STATEMENT w.                         *)
(* ------------------------------------------------------------------------- *)

let S2E_MONO_FROM_DERIV_EX = prove
 (`!f a b t1 t0.
     (!t. a < t /\ t < b ==> ?D. (f has_real_derivative D) (atreal t) /\ D <= &0) /\
     a < t1 /\ t1 <= t0 /\ t0 < b
     ==> f t0 <= f t1`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `f':real->real`) THEN
  MATCH_MP_TAC S2E_MONO_FROM_DERIV THEN
  MAP_EVERY EXISTS_TAC [`f':real->real`; `a:real`; `b:real`] THEN ASM_SIMP_TAC[]);;

(* The core: along an ancient flow pinched at arbitrarily negative times,   *)
(* R is constant on the closed connected surface at every time.             *)

let S2E_ENTROPY_FLOW_CONST = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^2))->bool) (h:real->A->real^2^2) b.
     hausdorff_space top /\ compact_space top /\ connected_space top /\
     (!a. a < b ==> ricci_flow_on (top,atlas) a b h) /\
     (!t x. t < b /\ x IN topspace top ==> &0 < mfd_scalar atlas (h t) x) /\
     (!e T. &0 < e
            ==> ?t. t < T /\ t < b /\
                    !x y. x IN topspace top /\ y IN topspace top
                          ==> mfd_scalar atlas (h t) x <= (&1 + e) * mfd_scalar atlas (h t) y)
     ==> !t x y. t < b /\ x IN topspace top /\ y IN topspace top
                 ==> mfd_scalar atlas (h t) x = mfd_scalar atlas (h t) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t0:real`; `x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(topspace top:A->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `AA = \s. mfd_integral (top,atlas) ((h:real->A->real^2^2) s) (topspace top)
                         (\x:A. &1)` THEN
  ABBREV_TAC `MM = \s. mfd_integral (top,atlas) ((h:real->A->real^2^2) s) (topspace top)
                         (mfd_scalar atlas (h s))` THEN
  ABBREV_TAC `EE = \s. mfd_integral (top,atlas) ((h:real->A->real^2^2) s) (topspace top)
                         (\x:A. mfd_scalar atlas (h s) x * log(mfd_scalar atlas (h s) x)) -
                       (MM:real->real) s * log(MM s / (AA:real->real) s)` THEN
  (* the static facts at any time s < b *)
  SUBGOAL_THEN
   `!s. s < b
        ==> &0 < (AA:real->real) s /\ &0 < (MM:real->real) s /\ &0 <= (EE:real->real) s /\
            (EE s = &0 ==> !z:A. z IN topspace top ==> mfd_scalar atlas (h s) z = MM s / AA s) /\
            (!e. (!x y:A. x IN topspace top /\ y IN topspace top
                          ==> mfd_scalar atlas ((h:real->A->real^2^2) s) x <=
                              (&1 + e) * mfd_scalar atlas (h s) y)
                 ==> EE s <= MM s * log(&1 + e))`
  (LABEL_TAC "STATIC") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ricci_flow_on (top,atlas:((A->bool)#(A->real^2))->bool) (s - &1) b h`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^2))->bool) /\
                  riemannian_metric atlas ((h:real->A->real^2^2) s)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ricci_flow_on (top,atlas:((A->bool)#(A->real^2))->bool) (s - &1) b h` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^2))->bool`;
                   `(h:real->A->real^2^2) s`; `mfd_scalar atlas ((h:real->A->real^2^2) s)`;
                   `(AA:real->real) s`; `(MM:real->real) s`] S2E_ENTROPY_STATIC) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["AA"; "MM"] THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC S2E_SCALAR_SMOOTH THEN EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "EE" THEN REWRITE_TAC[ETA_AX]];
    ALL_TAC] THEN
  (* for every e > 0, E(t0) <= m(t0) log(1 + e) *)
  SUBGOAL_THEN `!e. &0 < e ==> (EE:real->real) t0 <= (MM:real->real) t0 * log(&1 + e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e:real`; `t0:real`] o check (fun th -> is_forall(concl th) &&
      s2e_mentions "real_mul" th && s2e_mentions "real_lt" th &&
      not(s2e_mentions "ricci_flow_on" th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ricci_flow_on (top,atlas:((A->bool)#(A->real^2))->bool) (t1 - &2) b h`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(MM:real->real) t0 = MM t1` ASSUME_TAC THENL
     [MATCH_MP_TAC S2E_CONST_FROM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`t1 - &1`; `b:real`] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "MM" THEN
        MATCH_MP_TAC S2E_RF_MASS_DERIV THEN
        MAP_EVERY EXISTS_TAC [`t1 - &2`; `t1 - &1`; `b:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(EE:real->real) t0 <= EE t1` ASSUME_TAC THENL
     [MATCH_MP_TAC S2E_MONO_FROM_DERIV_EX THEN
      MAP_EVERY EXISTS_TAC [`t1 - &1`; `b:real`] THEN
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `s:real` THEN STRIP_TAC THEN EXPAND_TAC "EE" THEN
        MAP_EVERY EXPAND_TAC ["MM"; "AA"] THEN
        MATCH_MP_TAC S2E_RF_ENT_DERIV THEN
        MAP_EVERY EXISTS_TAC [`t1 - &2`; `t1 - &1`; `b:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "STATIC" (MP_TAC o SPEC `t1:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real` o last o CONJUNCTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* hence E(t0) = 0 *)
  USE_THEN "STATIC" (MP_TAC o SPEC `t0:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(EE:real->real) t0 = &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPECL [`(EE:real->real) t0`; `&0`; `(MM:real->real) t0`] S2E_LE_LIMIT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ADD_LID] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(MM:real->real) t0 * log(&1 + e)` THEN
    ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; LOG_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    s2e_mentions "mfd_scalar" th)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[]);;

(* The headline. *)

let S2E_S2_ENTROPY = prove
 (`!w:B->bool. P2B_REQ_S2_ENTROPY_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_REQ_S2_ENTROPY_STATEMENT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC S2E_ENTROPY_FLOW_CONST THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_diffeo (subtopology euclidean (sphere(vec 0:real^3,&1))) sphere2_atlas
                          (sphere(vec 0:real^3,&1)) (top:B topology)
                          (atlas:((B->bool)#(B->real^2))->bool) (topspace top)
                          (psi:real^3->B) (psi':B->real^3)` THEN
  REWRITE_TAC[mfd_diffeo; SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT; SUBTOPOLOGY_TOPSPACE] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `subtopology euclidean (sphere(vec 0:real^3,&1)) homeomorphic_space (top:B topology)`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphic_space] THEN
    MAP_EVERY EXISTS_TAC [`psi:real^3->B`; `psi':B->real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP HOMEOMORPHIC_COMPACT_SPACE th);
                                    GSYM(MATCH_MP HOMEOMORPHIC_CONNECTED_SPACE th)]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE];
    MATCH_MP_TAC CONNECTED_SPACE_SUBTOPOLOGY THEN REWRITE_TAC[CONNECTED_IN_EUCLIDEAN] THEN
    MATCH_MP_TAC CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC]);;

