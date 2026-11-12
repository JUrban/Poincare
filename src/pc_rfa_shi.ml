(* ========================================================================= *)
(* Unit pc_rfa_shi: global derivative estimates: the evolution of            *)
(* |nabla^m Rm|^2 on manifolds for every m, Shi's estimates with initial     *)
(* bounds on compact manifolds (RFA_SHI_GLOBAL_INITIAL) and the uniform      *)
(* equivalence of the metrics (RFA_METRIC_EQUIV, MT Lemma 3.15(1)).  The     *)
(* chart C^m bounds R1 built on them are in pc_rfa_r1.                       *)
(* ========================================================================= *)

needs "src/pc_rfa_rmderiv.ml";;
needs "src/pc_rfa_scalar.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* |nabla^m Rm|^2 on manifolds for every m: locality, chart                  *)
(* independence, joint smoothness and continuity, and the evolution          *)
(* inequality on a manifold, generalizing the m = 0 forms of pc_rfa_mfd.     *)
(* ========================================================================= *)

let RFA_LRM_NORM2_LOCAL = prove
 (`!m (G1:real^N->real^N^N) G2 s y.
        open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
        ==> lrm_deriv_norm2 m G1 y = lrm_deriv_norm2 m G2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lrm_deriv_norm2] THEN
  MATCH_MP_TAC LRG_LTNORM2_EQ THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`4`; `G1:real^N->real^N^N`; `G2:real^N->real^N^N`;
                 `lrm4 (G1:real^N->real^N^N)`; `lrm4 (G2:real^N->real^N^N)`;
                 `s:real^N->bool`] LRG_LNABLA_ITER_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`z:real^N`; `u:num->real^N`] THEN
    DISCH_TAC THEN REWRITE_TAC[lrm4] THEN ASM_SIMP_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LRIEMANN_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let RFA_RMD2_CHART = prove
 (`!m (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) c x.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        c IN atlas /\ x IN FST c
        ==> rfa_rmd2 m atlas g x = lrm_deriv_norm2 m (metric_local atlas c g) (SND c x)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `g:A->real^N^N`; `U:A->bool`; `phi:A->real^N`; `x:A`] THEN
  STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`,
           `cc:(A->bool)#(A->real^N)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in top (U:A->bool) /\ open_in top (V:A->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART);
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `V:A->bool`; `psi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:A->real^N) (U INTER V)) /\
                open(IMAGE (psi:A->real^N) (U INTER V))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THENL
     [EXISTS_TAC `U:A->bool`; EXISTS_TAC `V:A->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lrm_deriv_norm2 m
                (mpullback (chart_trans (U,phi) (V,psi))
                           (metric_local atlas (V,psi) (g:A->real^N^N))) (phi(x:A))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:num`; `IMAGE (psi:A->real^N) (U INTER V)`;
                   `IMAGE (phi:A->real^N) (U INTER V)`;
                   `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
                   `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
                   `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
                   `(phi:A->real^N) x`] LRM_DERIV_NORM2_PULLBACK) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
        EXISTS_TAC `IMAGE (psi:A->real^N) V` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                                         (g:A->real^N^N)` THEN
          REWRITE_TAC[riemannian_metric] THEN
          DISCH_THEN(MP_TAC o SPEC `(V:A->bool,psi:A->real^N)`) THEN
          ASM_REWRITE_TAC[FST; SND];
          SET_TAC[]];
        MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
        MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER]];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CHART_TRANS_AT THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_LRM_NORM2_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[IN_INTER];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x':A` THEN STRIP_TAC THEN
      MATCH_MP_TAC METRIC_LOCAL_TRANS THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[IN_INTER]]]);;


let RFA_LSMOOTH_LRM_NORM2 = prove
 (`!m U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lrm_deriv_norm2 m (G (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lrm_deriv_norm2; ltnorm2] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `i:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM_REAL THEN ASM_REWRITE_TAC[LRG_INDEX_TUPLES_FINITE] THEN
  X_GEN_TAC `j:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[RFA_LSMOOTH_LRM_DERIV] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_SIMP_TAC[RFA_LSMOOTH_LRM_DERIV] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_PRODUCT_REAL THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; LRG_LSMOOTH_GINV_ENTRY]);;

let RFA_RMD2_CHART_SMOOTH_M = prove
 (`!m (top:A topology) atlas a b (g:real->A->real^N^N) c.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas
     ==> smooth_map_on
           (interval(lift a,lift b) PCROSS IMAGE (SND c) (FST c INTER topspace top))
           (\z. lift(rfa_rmd2 m atlas (g (drop(fstcart z))) (chart_inv c (sndcart z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^N))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST c INTER topspace top = FST (c:(A->bool)#(A->real^N))` SUBST1_TAC THENL
   [MP_TAC(MATCH_MP OPEN_IN_SUBSET
      (ASSUME `open_in top (FST(c:(A->bool)#(A->real^N)))`)) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP RFA_LRICCI_FLOW_LSMOOTH) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. lift(lrm_deriv_norm2 m
                    ((\t. metric_local atlas (c:(A->bool)#(A->real^N))
                                       ((g:real->A->real^N^N) t)) (drop(fstcart z)))
                    (sndcart z))` THEN
  ASM_SIMP_TAC[RFA_LSMOOTH_LRM_NORM2; OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
              SNDCART_PASTECART; IN_INTERVAL_1; LIFT_DROP] THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `y:real^N`] THEN STRIP_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`m:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) (drop s)`; `c:(A->bool)#(A->real^N)`;
                 `chart_inv (c:(A->bool)#(A->real^N)) y`] RFA_RMD2_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                               (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let RFA_RMD2_EVOLUTION = prove
 (`!m. ?C. &0 <= C /\
     !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
      (g:real->A->real^N^N) t x.
        ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
        ==> ?d. ((\s. rfa_rmd2 m atlas (g s) x) has_real_derivative d) (atreal t) /\
                d <= rfa_lap atlas (g t) (rfa_rmd2 m atlas (g t)) x -
                     &2 * rfa_rmd2 (m + 1) atlas (g t) x +
                     C * sqrt(rfa_rmd2 m atlas (g t) x) *
                     sum(0..m) (\i. sqrt(rfa_rmd2 i atlas (g t) x) *
                                    sqrt(rfa_rmd2 (m - i) atlas (g t) x))`,
  GEN_TAC THEN
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A10"))
    (SPEC `m:num` (INST_TYPE [`:N`,`:N`] RFA_LRM_DERIV_NORM2_EVOLUTION)) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`; `x:A`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `a:real`; `b:real`; `g:real->A->real^N^N`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "A10" (MP_TAC o SPECL
   [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
           (FST(chart_at atlas x))`;
    `a:real`; `b:real`;
    `\t. metric_local (atlas:((A->bool)#(A->real^N))->bool) (chart_at atlas (x:A))
                      ((g:real->A->real^N^N) t)`;
    `t:real`; `SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN REWRITE_TAC[rfa_lap] THEN
  SUBGOAL_THEN
   `llap (metric_local atlas (chart_at atlas x) ((g:real->A->real^N^N) t))
         (\y. rfa_rmd2 m atlas (g t) (chart_inv (chart_at atlas (x:A)) y))
         (SND(chart_at atlas x) x) =
    llap (metric_local atlas (chart_at atlas x) (g t))
         (lrm_deriv_norm2 m (metric_local atlas (chart_at atlas x) (g t)))
         (SND(chart_at atlas x) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`m:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) t`;
                   `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`;
                   `chart_inv (chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) z`]
           RFA_RMD2_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_rmd2] THEN ASM_REWRITE_TAC[]);;


(* Joint continuity of |nabla^m Rm|^2 on [a,b) x M along a flow from a, by   *)
(* the generic tool of pc_rfa_scalar.                                        *)

let RFA_RMD2_CONTINUOUS_M = prove
 (`!m (top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N).
     ricci_flow_from (top,atlas) a b g
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. rfa_rmd2 m atlas (g (FST z)) (SND z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_rmd2] THEN
  MATCH_MP_TAC RFA_MQ_CONTINUOUS THEN
  REWRITE_TAC[RFA_LSMOOTH_LRM_NORM2] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LRM_NORM2_LOCAL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`m:num`; `top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`; `x:A`] RFA_RMD2_CHART) THEN
    ASM_REWRITE_TAC[rfa_rmd2] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[ricci_flow_from; ricci_flow_on];
    ASM_MESON_TAC[ricci_flow_from; ricci_flow_on];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `a:real`]
           RFA_RICCI_FLOW_FROM_EXT_AT) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* ========================================================================= *)
(* Shi's derivative estimates with initial bounds on a                       *)
(* compact manifold: by induction on m, the maximum principle for |D^m Rm|^2 *)
(* with the linear comparison ODE H' = A H + A.                              *)
(* ========================================================================= *)

let RFA_EXP_ODE = prove
 (`!A H0 a t.
     ((\s. (H0 + &1) * exp(A * (s - a)) - &1) has_real_derivative
      A * ((H0 + &1) * exp(A * (t - a)) - &1) + A) (atreal t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REAL_DIFF_CONV
    `((\s. (H0 + &1) * exp(A * (s - a)) - &1) has_real_derivative f') (atreal t)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

(* The real inequality behind the induction step: if every product          *)
(* sqrt(F_i) sqrt(F_(n-i)) is at most sqrt K (sqrt w + sqrt K) with w = F_n, *)
(* then C sqrt w sum_i (...) <= A w + A.                                     *)

let RFA_SHI_STEP_ARITH = prove
 (`!C4 K w n (tt:num->real).
     &0 <= C4 /\ &0 <= K /\ &0 <= w /\
     (!i. i <= n ==> tt i <= sqrt K * (sqrt w + sqrt K))
     ==> C4 * sqrt w * sum(0..n) tt <=
         (C4 * &(n + 1) * sqrt K * (&1 + sqrt K)) * w +
         C4 * &(n + 1) * sqrt K * (&1 + sqrt K)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt w /\ &0 <= sqrt K /\ sqrt w * sqrt w = w`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE; GSYM REAL_POW_2; SQRT_POW_2]; ALL_TAC] THEN
  ABBREV_TAC `s = sqrt w` THEN ABBREV_TAC `k = sqrt K` THEN
  SUBGOAL_THEN `sum(0..n) (tt:num->real) <= &(n + 1) * (k * (s + k))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0..n) (\i. k * (s + k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= w + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `s - &1` REAL_LE_POW_2) THEN
    UNDISCH_TAC `s * s = w` THEN UNDISCH_TAC `&0 <= w` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * s <= k * (w + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `P = C4 * &(n + 1) * k` THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C4 * s * (&(n + 1) * (k * (s + k)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `C4 * s * (&(n + 1) * (k * (s + k))) = P * (w + k * s)`
  SUBST1_TAC THENL
   [EXPAND_TAC "P" THEN UNDISCH_TAC `s * s = w` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(C4 * &(n + 1) * k * (&1 + k)) * w + C4 * &(n + 1) * k * (&1 + k) =
    P * ((&1 + k) * w + (&1 + k))`
  SUBST1_TAC THENL [EXPAND_TAC "P" THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `k * s <= k * (w + &1)` THEN UNDISCH_TAC `&0 <= w` THEN
  UNDISCH_TAC `&0 <= k` THEN REAL_ARITH_TAC);;

(* A bound for the initial slice of a jointly continuous function on        *)
(* [a,b) x M, M compact.                                                     *)

let RFA_COMPACT_SLICE_BOUND = prove
 (`!(top:A topology) (f:real->A->real) a b.
     compact_space top /\ a < b /\
     continuous_map
       (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                      (subtopology top (topspace top)),
        euclideanreal) (\z. f (FST z) (SND z))
     ==> ?H0. &0 <= H0 /\ !x. x IN topspace top ==> f a x <= H0`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `topspace (top:A topology) = {}` THENL
   [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`; `top:A topology`;
                 `topspace (top:A topology)`; `f:real->A->real`; `a:real`]
         RFA_SUP_COMPACT_ATTAINED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM compact_space] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV;
                IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs((f:real->A->real) a y)` THEN REWRITE_TAC[REAL_ABS_POS] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(f:real->A->real) a y` THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* Each product sqrt(F_i) sqrt(F_(n-i)) is at most sqrt K (sqrt F_n + sqrt K) *)
(* when all F_j with j < n are bounded by K.                                 *)

let RFA_SHI_TERM_BOUND = prove
 (`!n K (Fv:num->real).
     ~(n = 0) /\ &0 <= K /\ (!j. &0 <= Fv j) /\ (!j. j < n ==> Fv j <= K)
     ==> !i. i <= n ==> sqrt(Fv i) * sqrt(Fv (n - i)) <= sqrt K * (sqrt(Fv n) + sqrt K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!j. &0 <= sqrt((Fv:num->real) j)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt K` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < n ==> sqrt((Fv:num->real) j) <= sqrt K` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `i = 0` THENL
   [ASM_REWRITE_TAC[SUB_0] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = n` THENL
   [ASM_REWRITE_TAC[SUB_REFL] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt K` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MP_TAC(SPEC `n:num` (ASSUME `!j. &0 <= sqrt((Fv:num->real) j)`)) THEN
      REAL_ARITH_TAC]]);;

(* RFA_SHI_GLOBAL_INITIAL: |nabla^m Rm|^2 is bounded on [a,b) x M for every  *)
(* m, given a bound on |Rm|^2.                                               *)

let RFA_SHI_GLOBAL_INITIAL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) B.
      compact_space top /\ ricci_flow_from (top,atlas) a b g /\
      (!t x. a <= t /\ t < b /\ x IN topspace top ==> rfa_rmd2 0 atlas (g t) x <= B)
      ==> !m. ?C. !t x. a <= t /\ t < b /\ x IN topspace top
                        ==> rfa_rmd2 m atlas (g t) x <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                  (g:real->A->real^N^N) /\
    smooth_manifold_atlas top atlas /\ a < b /\
    (!t. a <= t /\ t < b ==> riemannian_metric atlas (g t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_THEN(LABEL_TAC "wf") THEN
  ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "wf" (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Cj:num->real` (LABEL_TAC "ih")) THEN
  ABBREV_TAC `K = sum(0..n) (\j. abs((Cj:num->real) j))` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j t x. j < n /\ a <= t /\ t < b /\ x IN topspace top
            ==> rfa_rmd2 j atlas ((g:real->A->real^N^N) t) x <= K`
  (LABEL_TAC "kb") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs((Cj:num->real) j)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= c ==> x <= abs c`) THEN
      USE_THEN "ih" (MP_TAC o SPECL [`t:real`; `x:A`] o
                     C MP (ASSUME `(j:num) < n`) o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "K" THEN
      MP_TAC(ISPECL [`\j. abs((Cj:num->real) j)`;
                     `sum(0..n) (\j. abs((Cj:num->real) j))`; `0..n`] SUM_POS_BOUND) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_REFL; LE_0; REAL_ABS_POS] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_CHOOSE_THEN `C4:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b4"))
    (SPEC `n:num` RFA_RMD2_EVOLUTION) THEN
  ABBREV_TAC `AA = C4 * &(n + 1) * sqrt K * (&1 + sqrt K)` THEN
  SUBGOAL_THEN `&0 <= AA` ASSUME_TAC THENL
   [EXPAND_TAC "AA" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`;
                 `\t x. rfa_rmd2 n (atlas:((A->bool)#(A->real^N))->bool)
                                 ((g:real->A->real^N^N) t) (x:A)`;
                 `a:real`; `b:real`] RFA_COMPACT_SLICE_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_RMD2_CONTINUOUS_M THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `topspace (top:A topology)`; `a:real`; `b:real`;
                 `g:real->A->real^N^N`;
                 `\t x. rfa_rmd2 n (atlas:((A->bool)#(A->real^N))->bool)
                                 ((g:real->A->real^N^N) t) (x:A)`;
                 `\t:real u:real. AA * u + AA`;
                 `\t. (H0 + &1) * exp(AA * (t - a)) - &1`] RFA_MAXP_SCALAR) THEN
  REWRITE_TAC[ETA_AX] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM compact_space; OPEN_IN_TOPSPACE] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC RFA_RMD2_CONTINUOUS_M THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_RMD2_CHART_SMOOTH_M THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
      USE_THEN "b4" (MP_TAC o SPECL [`top:A topology`;
        `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
        `g:real->A->real^N^N`; `t:real`; `x:A`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                      ((g:real->A->real^N^N) t)` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `!j. &0 <= rfa_rmd2 j (atlas:((A->bool)#(A->real^N))->bool)
                                  ((g:real->A->real^N^N) t) x`
      ASSUME_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC RFA_RMD2_POS THEN EXISTS_TAC `top:A topology` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`n:num`; `K:real`;
                     `\j. rfa_rmd2 j (atlas:((A->bool)#(A->real^N))->bool)
                                  ((g:real->A->real^N^N) t) (x:A)`]
             RFA_SHI_TERM_BOUND) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "kb" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        DISCH_TAC] THEN
      MP_TAC(ISPECL [`C4:real`; `K:real`;
                     `rfa_rmd2 n (atlas:((A->bool)#(A->real^N))->bool)
                               ((g:real->A->real^N^N) t) (x:A)`; `n:num`;
                     `\i. sqrt(rfa_rmd2 i (atlas:((A->bool)#(A->real^N))->bool)
                                       ((g:real->A->real^N^N) t) (x:A)) *
                          sqrt(rfa_rmd2 (n - i) atlas (g t) x)`]
             RFA_SHI_STEP_ARITH) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `n + 1` (ASSUME `!j. &0 <= rfa_rmd2 j
        (atlas:((A->bool)#(A->real^N))->bool) ((g:real->A->real^N^N) t) (x:A)`)) THEN
      UNDISCH_TAC
       `d <= rfa_lap (atlas:((A->bool)#(A->real^N))->bool) ((g:real->A->real^N^N) t)
                     (rfa_rmd2 n atlas (g t)) (x:A) -
             &2 * rfa_rmd2 (n + 1) atlas (g t) x +
             C4 * sqrt(rfa_rmd2 n atlas (g t) x) *
             sum(0..n) (\i. sqrt(rfa_rmd2 i atlas (g t) x) *
                            sqrt(rfa_rmd2 (n - i) atlas (g t) x))` THEN
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN EXISTS_TAC `AA:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `(a * u + a) - (a * v + a) = a * (u - v)`;
                  REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= a ==> abs a = a`; REAL_LE_REFL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REWRITE_TAC[RFA_EXP_ODE];
      REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= h ==> x <= (h + &1) - &1`]];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(H0 + &1) * exp(AA * (b - a))` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(H0 + &1) * exp(AA * (t - a)) - &1` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &1 <= y`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC]]);;

(* ========================================================================= *)
(* Uniform equivalence of the metrics under bounded Ricci                    *)
(* curvature (MT Lemma 3.15(1), CLN Cor 6.11).                               *)
(* ========================================================================= *)

(* The time derivative of the quadratic form v.(g x)v along a Ricci flow.    *)

let RFA_QFORM_EXPAND = prove
 (`!(A:real^N^N) v.
     v dot (A ** v) =
     sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. v$i * A$i$j * v$j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[matrix_vector_mul; LAMBDA_BETA] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN REAL_ARITH_TAC);;

let RFA_QFORM_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) t x v.
     ricci_flow_on (top,atlas) a b g /\ a < t /\ t < b /\ x IN topspace top
     ==> ((\s. v dot (g s x ** v)) has_real_derivative
          --(&2) * mfd_ricci atlas (g t) x v v) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology) atlas /\
                riemannian_metric atlas ((g:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_ricci atlas ((g:real->A->real^N^N) t) (x:A) v v =
    v dot (mfd_ricci_matrix atlas (g t) x ** v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_ricci_matrix; mfd_ricci] THEN
    MATCH_MP_TAC LRG_LRICCI_DOT_FORM THEN
    EXISTS_TAC `IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                      (FST(chart_at atlas x))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^N))->bool)
                     ((g:real->A->real^N^N) t)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[RFA_QFORM_EXPAND] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN
   `((\s. (g:real->A->real^N^N) s x$i$j) has_real_derivative
     --(&2) * mfd_ricci_matrix atlas (g t) x$i$j) (atreal t)`
  MP_TAC THENL
   [UNDISCH_TAC `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                   a b (g:real->A->real^N^N)` THEN
    REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(v:real^N)$j` o MATCH_MP HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
  DISCH_THEN(MP_TAC o SPEC `(v:real^N)$i` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

(* A real-valued slice of a smooth map is continuous in time.                *)

let RFA_TSLICE_CONTINUOUS = prove
 (`!W (FF:real^(1,N)finite_sum->real^P) (L:real^P->real^1) y0 s.
     open W /\ smooth_map_on W FF /\ linear L /\ pastecart (lift s) y0 IN W
     ==> (\r. drop(L(FF(pastecart (lift r) y0)))) real_continuous (atreal s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
  SUBGOAL_THEN
   `lift o (\r. drop((L:real^P->real^1)
                   ((FF:real^(1,N)finite_sum->real^P) (pastecart (lift r) y0)))) o drop =
    L o FF o (\s1. pastecart s1 (y0:real^N))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_AT_ID; CONTINUOUS_CONST];
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN ASM_REWRITE_TAC[]]);;

let RFA_EXP_AFFINE_CONTINUOUS = prove
 (`!c a s. (\x. exp(c * (x - a))) real_continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
  EXISTS_TAC `exp(c * (x - a)) * c` THEN
  MP_TAC(REAL_DIFF_CONV `((\x. exp(c * (x - a))) has_real_derivative f') (atreal x)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let RFA_EXP_AFFINE_DERIV = prove
 (`!k a x. ((\s. exp(k * (s - a))) has_real_derivative exp(k * (x - a)) * k)
           (atreal x)`,
  REPEAT GEN_TAC THEN
  MP_TAC(REAL_DIFF_CONV `((\s. exp(k * (s - a))) has_real_derivative f') (atreal x)`) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let RFA_MVT_MONO = prove
 (`!(f:real->real) f' a t.
     a < t /\ f real_continuous_on real_interval[a,t] /\
     (!s. a < s /\ s < t ==> (f has_real_derivative f' s) (atreal s)) /\
     (!s. a < s /\ s < t ==> &0 <= f' s)
     ==> f a <= f t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real->real`; `a:real`; `t:real`] REAL_MVT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= (f':real->real) z * (t - a)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Two-sided Gronwall bound: |q'| <= c q on (a,t) and q continuous on [a,t] *)
(* give exp(-c(t-a)) q(a) <= q(t) <= exp(c(t-a)) q(a).                      *)

let RFA_GRONWALL_2SIDED = prove
 (`!(q:real->real) q' c a t.
     a < t /\ q real_continuous_on real_interval[a,t] /\
     (!s. a < s /\ s < t ==> (q has_real_derivative q' s) (atreal s)) /\
     (!s. a < s /\ s < t ==> abs(q' s) <= c * q s)
     ==> exp(--(c * (t - a))) * q a <= q t /\ q t <= exp(c * (t - a)) * q a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\s. exp(c * (s - a)) * (q:real->real) s`;
      `\s. exp(c * (s - a)) * (q':real->real) s + (exp(c * (s - a)) * c) * q s`;
      `a:real`; `t:real`] RFA_MVT_MONO) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
        ASM_REWRITE_TAC[RFA_EXP_AFFINE_CONTINUOUS];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
        ASM_SIMP_TAC[RFA_EXP_AFFINE_DERIV];
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[REAL_RING `!e x c y:real. e * x + (e * c) * y = e * (x + c * y)`] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(c * (t - a))) * (exp(c * (t - a)) * (q:real->real) t)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL2; REAL_MUL_LID; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. --(exp(--c * (s - a)) * (q:real->real) s)`;
    `\s. --(exp(--c * (s - a)) * (q':real->real) s + (exp(--c * (s - a)) * --c) * q s)`;
    `a:real`; `t:real`] RFA_MVT_MONO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[RFA_EXP_AFFINE_CONTINUOUS];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
      ASM_SIMP_TAC[RFA_EXP_AFFINE_DERIV];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_RING `!e x c y:real.
                    --(e * x + (e * --c) * y) = e * (c * y - x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_EXP_0; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_LE_NEG2] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(c * (t - a)) * (exp(--(c * (t - a))) * (q:real->real) t)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC; REAL_EXP_NEG_MUL; REAL_MUL_LID; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE]]);;

(* The metric equivalence RFA_METRIC_EQUIV.                                   *)

let RFA_METRIC_EQUIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
    (g:real->A->real^N^N) K.
      ricci_flow_from (top,atlas) a b g /\
      (!t x v. a <= t /\ t < b /\ x IN topspace top
               ==> abs(mfd_ricci atlas (g t) x v v) <= K * (v dot (g t x ** v)))
      ==> !t x v. a <= t /\ t < b /\ x IN topspace top
                  ==> exp(--(&2 * K * (t - a))) * (v dot (g a x ** v))
                      <= v dot (g t x ** v) /\
                      v dot (g t x ** v) <= exp(&2 * K * (t - a)) * (v dot (g a x ** v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ric")) THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `v:real^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ricci_flow_on (top:A topology,atlas:((A->bool)#(A->real^N))->bool) a b
                  (g:real->A->real^N^N) /\
    smooth_manifold_atlas top atlas`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_from; ricci_flow_on]; ALL_TAC] THEN
  ASM_CASES_TAC `t:real = a` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0;
                    REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `ricci_flow_from (top:A topology,atlas:((A->bool)#(A->real^N))->bool)
                 a b (g:real->A->real^N^N)` THEN
  REWRITE_TAC[ricci_flow_from] THEN
  DISCH_THEN(MP_TAC o SPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)` o
             last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `y0 = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)) x` THEN
  SUBGOAL_THEN `y0 IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                             (FST(chart_at atlas x))` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. v dot ((g:real->A->real^N^N) s x ** v)`;
                 `\s. --(&2) * mfd_ricci atlas ((g:real->A->real^N^N) s) (x:A) v v`;
                 `&2 * K`; `a:real`; `t:real`] RFA_GRONWALL_2SIDED) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC
       `\r. drop((\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v)))
                 ((FF:real^(1,N)finite_sum->real^(N,N)finite_prod)
                  (pastecart (lift r) y0)))` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        REWRITE_TAC[LIFT_DROP] THEN
        SUBGOAL_THEN
         `(FF:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart (lift r) y0) =
          vectorize(metric_local atlas (chart_at atlas (x:A))
                                 ((g:real->A->real^N^N) r) y0)`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[MATRIFY_VECTORIZE] THEN EXPAND_TAC "y0" THEN
        MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `(g:real->A->real^N^N) r`; `x:A`] METRIC_LOCAL_AT) THEN
        ASM_SIMP_TAC[];
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MP_TAC(ISPECL
         [`interval(lift(a - e),lift b) PCROSS
           IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) (x:A)))
                 (FST(chart_at atlas x))`;
          `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`;
          `\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v))`;
          `y0:real^N`; `r:real`] RFA_TSLICE_CONTINUOUS) THEN
        REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS;
                       IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[]]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_QFORM_DERIV THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      USE_THEN "ric" (MP_TAC o SPECL [`s:real`; `x:A`; `v:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC[]]);;

