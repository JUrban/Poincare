(* ========================================================================= *)
(* Unit pc_rfa_tmaxp: the Rayleigh barrier for lambda = mfd_sec_min along a  *)
(* 3D Ricci flow (RFA_SECMIN_BARRIER) and the preservation of                *)
(* lambda >= delta >= 0 on a compact open set (RFA_SECMIN_LOWER_PRESERVED),  *)
(* the core of the statements P2C_REQ_SEC_PRESERVED (A13) and P2_THM_4_23    *)
(* proved in pc_rfa_secpres.                                                 *)
(* ========================================================================= *)

needs "src/pc_rfa_secmin.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* Time derivatives along a local flow and the reaction term                 *)
(* 2 (p1^2 + p2 p3) of the Rayleigh quotient at a minimizing eigenvector.    *)
(* ========================================================================= *)

(* Copy of RFA_LQFORM_DERIV (pc_rfa_slcut.ml, same statement and proof):    *)
(* pc_rfa_slcut is not in this load closure and is heavy to load.          *)

let RFA_GQFORM_DERIV = prove
 (`!U a b (G:real->real^N->real^N^N) t y v.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. v dot (G s y ** v)) has_real_derivative --(&2) * lricci (G t) y v v)
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) t`; `y:real^N`;
                 `v:real^N`; `v:real^N`] LRG_LRICCI_DOT_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_QFORM_EXPAND] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN
  SUBGOAL_THEN
   `((\s. (G:real->real^N->real^N^N) s y$i$j) has_real_derivative
     --(&2) * lricci (G t) y (basis i) (basis j)) (atreal t)`
  MP_TAC THENL
   [UNDISCH_TAC `lricci_flow U a b (G:real->real^N->real^N^N)` THEN
    REWRITE_TAC[lricci_flow] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(v:real^N)$j` o MATCH_MP HAS_REAL_DERIVATIVE_RMUL_ATREAL) THEN
  DISCH_THEN(MP_TAC o SPEC `(v:real^N)$i` o MATCH_MP HAS_REAL_DERIVATIVE_LMUL_ATREAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

(* The time derivative of P(e,e) = (R/2) g(e,e) - Ric(e,e) along a local    *)
(* Ricci flow in dimension 3 (fixed vector e).                               *)

let RFA_PCURV_TIME_DERIV = prove
 (`!U a b (G:real->real^3->real^3^3) t y e.
     lricci_flow U a b G /\ a < t /\ t < b /\ y IN U
     ==> ((\s. lpcurv (G s) y (\m. e)) has_real_derivative
          (llap (G t) (lscalar (G t)) y / &2 + ltnorm2 2 (G t) (lric2 (G t)) y) *
          (e dot (G t y ** e)) -
          lscalar (G t) y * lricci (G t) y e e -
          (ltlap 2 (G t) (lric2 (G t)) y (\m. e) +
           &3 * lscalar (G t) y * lricci (G t) y e e -
           &6 * sum(1..3) (\p. sum(1..3) (\q.
                  matrix_inv(G t y)$p$q * lricci (G t) y e (basis p) *
                  lricci (G t) y (basis q) e)) +
           (&2 * ltnorm2 2 (G t) (lric2 (G t)) y - lscalar (G t) y pow 2) *
           (e dot (G t y ** e)))) (atreal t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RFA_LPCURV_DIAG] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `t:real`; `y:real^3`; `e:real^3`; `e:real^3`]
         RFA_LRICCI_EVOLUTION_3D) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `t:real`; `y:real^3`; `e:real^3`] RFA_GQFORM_DERIV) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `t:real`; `y:real^3`] LSCALAR_EVOLUTION) THEN
  ASM_REWRITE_TAC[COND_ID] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. lscalar ((G:real->real^3->real^3^3) s) y / &2) has_real_derivative
     (llap (G t) (lscalar (G t)) y + &2 * ltnorm2 2 (G t) (lric2 (G t)) y) / &2)
    (atreal t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\s. lscalar ((G:real->real^3->real^3^3) s) y / &2 * (e dot (G s y ** e)) -
          lricci (G s) y e e) has_real_derivative
     (lscalar (G t) y / &2 * (--(&2) * lricci (G t) y e e) +
      (llap (G t) (lscalar (G t)) y + &2 * ltnorm2 2 (G t) (lric2 (G t)) y) / &2 *
      (e dot (G t y ** e))) -
     (ltlap 2 (G t) (lric2 (G t)) y (\m. e) +
      &3 * lscalar (G t) y * lricci (G t) y e e -
      &6 * sum(1..3) (\p. sum(1..3) (\q.
             matrix_inv(G t y)$p$q * lricci (G t) y e (basis p) *
             lricci (G t) y (basis q) e)) +
      (&2 * ltnorm2 2 (G t) (lric2 (G t)) y - lscalar (G t) y pow 2) *
      (e dot (G t y ** e)))) (atreal t)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  REAL_ARITH_TAC);;

(* The reaction term of the evolution of the Rayleigh quotient at a        *)
(* minimizing eigenvector: 2 (p1^2 + p2 p3).                                *)

let RFA_REACTION_RING = prove
 (`!r1 r2 r3:real.
     (r1 + r2 + r3) pow 2 - (r1 pow 2 + r2 pow 2 + r3 pow 2) -
     &4 * (r1 + r2 + r3) * r1 + &6 * r1 pow 2 +
     &2 * ((r1 + r2 + r3) / &2 - r1) * r1 =
     &2 * (((r1 + r2 + r3) / &2 - r1) pow 2 +
           ((r1 + r2 + r3) / &2 - r2) * ((r1 + r2 + r3) / &2 - r3))`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let RFA_BARRIER_REACTION = prove
 (`!U a b (G:real->real^3->real^3^3) t0 y0 (S:real^3^3).
     lricci_flow U a b G /\ a < t0 /\ t0 < b /\ y0 IN U /\
     invertible S /\ matrix_inv(G t0 y0) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci (G t0) y0 (transp S ** basis i) (transp S ** basis j) = &0)
     ==> ((\s. lpcurv (G s) y0 (\m. transp S ** basis 1) /
               ((transp S ** basis 1) dot (G s y0 ** (transp S ** basis 1))))
          has_real_derivative
          ltlap 2 (G t0) (lpcurv (G t0)) y0 (\m. transp S ** basis 1) +
          &2 * (lpcurv (G t0) y0 (\m. transp S ** basis 1) pow 2 +
                lpcurv (G t0) y0 (\m. transp S ** basis 2) *
                lpcurv (G t0) y0 (\m. transp S ** basis 3))) (atreal t0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^3->real^3^3) t0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lricci_flow]; ALL_TAC] THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field U ((G:real->real^3->real^3^3) t0)`)
          (ASSUME `(y0:real^3) IN U`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp(S:real^3^3) ** basis i) dot
              ((G:real->real^3->real^3^3) t0 y0 ** (transp S ** basis j)) =
              if i = j then &1 else &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  ABBREV_TAC `f1 = transp(S:real^3^3) ** basis 1` THEN
  ABBREV_TAC `f2 = transp(S:real^3^3) ** basis 2` THEN
  ABBREV_TAC `f3 = transp(S:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN
   `f1 dot ((G:real->real^3->real^3^3) t0 y0 ** f1) = &1 /\
    f2 dot (G t0 y0 ** f2) = &1 /\ f3 dot (G t0 y0 ** f3) = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f1"; "f2"; "f3"] THEN ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `lricci ((G:real->real^3->real^3^3) t0) y0 f1 f2 = &0 /\
    lricci (G t0) y0 f1 f3 = &0 /\ lricci (G t0) y0 f2 f1 = &0 /\
    lricci (G t0) y0 f2 f3 = &0 /\ lricci (G t0) y0 f3 f1 = &0 /\
    lricci (G t0) y0 f3 f2 = &0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["f1"; "f2"; "f3"] THEN ASM_SIMP_TAC[ARITH]; ALL_TAC] THEN
  (* frame values of R, |Ric|^2 and Ric^2(e,e) *)
  SUBGOAL_THEN
   `lscalar ((G:real->real^3->real^3^3) t0) y0 =
    lricci (G t0) y0 f1 f1 + lricci (G t0) y0 f2 f2 + lricci (G t0) y0 f3 f3`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                   `S:real^3^3`] RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 2 ((G:real->real^3->real^3^3) t0) (lric2 (G t0)) y0 =
    lricci (G t0) y0 f1 f1 pow 2 + lricci (G t0) y0 f2 f2 pow 2 +
    lricci (G t0) y0 f3 f3 pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                   `S:real^3^3`] RFA_RICNORM_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..3) (\p. sum(1..3) (\q.
       matrix_inv((G:real->real^3->real^3^3) t0 y0)$p$q * lricci (G t0) y0 f1 (basis p) *
       lricci (G t0) y0 (basis q) f1)) = lricci (G t0) y0 f1 f1 pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                   `S:real^3^3`; `f1:real^3`; `f1:real^3`] RFA_RIC2_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `t0:real`; `y0:real^3`; `f1:real^3`] RFA_GQFORM_DERIV) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `a:real`; `b:real`; `G:real->real^3->real^3^3`;
                 `t0:real`; `y0:real^3`; `f1:real^3`] RFA_PCURV_TIME_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun thf -> DISCH_THEN(fun thg ->
    MP_TAC(BETA_RULE(MATCH_MP (MATCH_MP (REWRITE_RULE[IMP_CONJ]
                                           HAS_REAL_DERIVATIVE_DIV_ATREAL) thf) thg)))) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH; REAL_POW_ONE; REAL_DIV_1; REAL_MUL_RID] THEN
  MATCH_MP_TAC(MESON[]
   `(x:real) = y ==> (f has_real_derivative x) net ==> (f has_real_derivative y) net`) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `(G:real->real^3->real^3^3) t0`; `y0:real^3`;
                 `\m:num. (f1:real^3)`] RFA_LTLAP2_LPCURV) THEN
  ASM_REWRITE_TAC[lmetric2] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RFA_LPCURV_DIAG] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`lricci ((G:real->real^3->real^3^3) t0) y0 f1 f1`;
                `lricci ((G:real->real^3->real^3^3) t0) y0 f2 f2`;
                `lricci ((G:real->real^3->real^3^3) t0) y0 f3 f3`] RFA_REACTION_RING) THEN
  REAL_ARITH_TAC);;


(* ========================================================================= *)
(* Smoothness of the barrier and the Rayleigh barrier for                    *)
(* lambda = mfd_sec_min at any point of a 3D Ricci flow (RFA_SECMIN_BARRIER). *)
(* ========================================================================= *)

(* Smoothness of the Rayleigh barrier P(E,E) / g(E,E) where E does not vanish. *)

let RFA_RQ_EXT_SMOOTH = prove
 (`!U W (G:real^N->real^N^N) y0 e.
     metric_field U G /\ y0 IN U /\ open W /\ W SUBSET U /\
     (!y. y IN W ==> ~(e - christoffel G y0 (y - y0) e = vec 0))
     ==> smooth_map_on W
           (\y. lift(lpcurv G y (\m. e - christoffel G y0 (y - y0) e) /
                     ((e - christoffel G y0 (y - y0) e) dot
                      (G y ** (e - christoffel G y0 (y - y0) e)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LPCURV_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `lpcurv (G:real^N->real^N^N)`; `y0:real^N`; `e:real^N`]
         RFA_EXT_EVAL_SMOOTH) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`; `y0:real^N`; `e:real^N`]
         RFA_EXT_EVAL_SMOOTH) THEN
  ASM_REWRITE_TAC[lmetric2] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC
   `\y. lift(drop(lift(lpcurv (G:real^N->real^N^N) y
                         (\m. e - christoffel G y0 (y - y0) e))) /
             drop(lift((e - christoffel G y0 (y - y0) e) dot
                       (G y ** (e - christoffel G y0 (y - y0) e)))))` THEN
  CONJ_TAC THENL [REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
  MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let RFA_SECMIN_BARRIER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) U t0 x0.
     ricci_flow_on (top,atlas) a b g /\ open_in top U /\ a < t0 /\ t0 < b /\ x0 IN U
     ==> ?d W (phi:real->real^3->real) D p2 p3.
           &0 < d /\ open W /\ SND(chart_at atlas x0) x0 IN W /\
           W SUBSET IMAGE (SND(chart_at atlas x0)) (FST(chart_at atlas x0) INTER U) /\
           (!y. y IN W
                ==> mfd_sec_min atlas (g t0) (chart_inv (chart_at atlas x0) y) <=
                    phi t0 y) /\
           phi t0 (SND(chart_at atlas x0) x0) = mfd_sec_min atlas (g t0) x0 /\
           (!t. t0 - d < t /\ t <= t0
                ==> mfd_sec_min atlas (g t) x0 <= phi t (SND(chart_at atlas x0) x0)) /\
           smooth_map_on W (\y. lift(phi t0 y)) /\
           ((\t. phi t (SND(chart_at atlas x0) x0)) has_real_derivative D)
             (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
           mfd_sec_min atlas (g t0) x0 <= p2 /\ mfd_sec_min atlas (g t0) x0 <= p3 /\
           p2 <= sqrt(rfa_rmd2 0 atlas (g t0) x0) /\
           p3 <= sqrt(rfa_rmd2 0 atlas (g t0) x0) /\
           (((\y. lift(phi t0 y)) has_derivative (\v. vec 0))
              (at (SND(chart_at atlas x0) x0))
            ==> llap (metric_local atlas (chart_at atlas x0) (g t0)) (phi t0)
                     (SND(chart_at atlas x0) x0) +
                &2 * (mfd_sec_min atlas (g t0) x0 pow 2 + p2 * p3) = D)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`;
                 `U:A->bool`] RFA_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^3)) x0` THEN
  ABBREV_TAC `V = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) /\
    (y0:real^3) IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ASSUME `lricci_flow V a b
        (\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))`) THEN
      REWRITE_TAC[lricci_flow] THEN
      DISCH_THEN(MP_TAC o SPEC `t0:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["y0"; "V"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `c:(A->bool)#(A->real^3)`; `x0:A`]
         RFA_SECMIN_CHART_3D) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^3->bool`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                 `y0:real^3`; `S:real^3^3`] RFA_P3_MIN_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `f1 = transp(S:real^3^3) ** basis 1` THEN
  ABBREV_TAC `f2 = transp(S:real^3^3) ** basis 2` THEN
  ABBREV_TAC `f3 = transp(S:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN
   `f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y0 - y0) f1 = f1` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_EXT_AT THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f1:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f1) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)
        ==> y IN V /\ chart_inv c y IN FST c /\ SND c (chart_inv c y) = y`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN V` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN UNDISCH_TAC
       `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)` THEN
      SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                  ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)} =
      IMAGE (SND c) (FST c INTER U) INTER
      {y | (\y. f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1) y IN (:real^3) DIFF {vec 0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h. --(christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 h f1)` THEN
    MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN {y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)} SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))`) (ASSUME `(y0:real^3) IN V`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp(S:real^3^3) ** basis i) dot
              (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** (transp S ** basis j)) = if i = j then &1 else &0`
  (LABEL_TAC "orth") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f2 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &1 /\ f3 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &1 /\
    f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &0 /\ f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &0 /\
    f2 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &0 /\ f3 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "orth" (fun th ->
      MAP_EVERY (fun (i,j) -> MP_TAC(SPECL [mk_small_numeral i; mk_small_numeral j] th))
        [2,2; 3,3; 1,2; 1,3; 2,3; 3,2]) THEN
    REWRITE_TAC[ARITH; ASSUME `transp(S:real^3^3) ** basis 1 = f1`;
                ASSUME `transp(S:real^3^3) ** basis 2 = f2`;
                ASSUME `transp(S:real^3^3) ** basis 3 = f3`] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t0 - a:real` THEN
  EXISTS_TAC
   `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}` THEN
  EXISTS_TAC
   `\t y. lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)) y
            (\m. f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1) /
          ((f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1) dot
           (metric_local atlas c (g t) y **
            (f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1)))` THEN
  EXISTS_TAC
   `ltlap 2 (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) (lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))) y0 (\m. f1) +
    &2 * (lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1) pow 2 +
          lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f2) * lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f3))` THEN
  EXISTS_TAC `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f2)` THEN
  EXISTS_TAC `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f3)` THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* d > 0 *)
    ASM_REAL_ARITH_TAC;
    (* W SUBSET IMAGE *)
    SET_TAC[];
    (* spatial barrier *)
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)`)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `c:(A->bool)#(A->real^3)`;
                   `chart_inv (c:(A->bool)#(A->real^3)) y`;
                   `f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1`] RFA_SECMIN_RAYLEIGH) THEN
    ASM_SIMP_TAC[];
    (* value at y0 *)
    REWRITE_TAC[REAL_DIV_1];
    (* time barrier *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`; `x0:A`;
                   `f1:real^3`] RFA_SECMIN_RAYLEIGH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    (* smoothness *)
    MATCH_MP_TAC RFA_RQ_EXT_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM];
    (* derivative *)
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(BETA_RULE(ISPECL [`V:real^3->bool`; `a:real`; `b:real`;
       `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
       `t0:real`; `y0:real^3`; `S:real^3^3`] RFA_BARRIER_REACTION)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    (* p2 bound *)
    MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`;
                   `f1:real^3`; `f3:real^3`; `f2:real^3`] RFA_LSECTIONAL_PCURV_3D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`] LRG_METRIC_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `x0:A`; `f1:real^3`; `f3:real^3`]
           RFA_MFD_SECTIONAL_LE_RMD2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_ORTHO_NONCOLLINEAR THEN
      EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    (* p3 bound *)
    MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`;
                   `f1:real^3`; `f2:real^3`; `f3:real^3`] RFA_LSECTIONAL_PCURV_3D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`] LRG_METRIC_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `x0:A`; `f1:real^3`; `f2:real^3`]
           RFA_MFD_SECTIONAL_LE_RMD2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_ORTHO_NONCOLLINEAR THEN
      EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    (* llap *)
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `x = y ==> x + z = y + z:real`) THEN
    MATCH_MP_TAC RFA_BARRIER_LAP THEN
    MAP_EVERY EXISTS_TAC
     [`V:real^3->bool`; `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`; `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1)`] THEN
    ASM_REWRITE_TAC[lmetric2] THEN SIMP_TAC[IN_ELIM_THM]]);;


(* ========================================================================= *)
(* The reaction lower bound, compactness helpers, and the                    *)
(* preservation of lambda >= delta >= 0 (RFA_SECMIN_LOWER_PRESERVED).        *)
(* ========================================================================= *)

(* The reaction is bounded below by 2 C min(lambda,0) when the other two  *)
(* eigenvalues lie in [lambda, C].                                          *)

let RFA_REACTION_LOWER = prove
 (`!p1 p2 p3 C.
     p1 <= p2 /\ p1 <= p3 /\ p2 <= C /\ p3 <= C /\ &0 <= C
     ==> &2 * C * min p1 (&0) <= &2 * (p1 pow 2 + p2 * p3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p1 pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= p1` THENL
   [SUBGOAL_THEN `&0 <= p2 * p3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= p1 ==> min p1 (&0) = &0`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(&0 <= p1) ==> min p1 (&0) = p1`] THEN
  SUBGOAL_THEN `C * p1 <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= C * --p1 ==> C * p1 <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= p2 /\ &0 <= p3` THENL
   [SUBGOAL_THEN `&0 <= p2 * p3` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `p2 < &0 /\ p3 < &0` THENL
   [SUBGOAL_THEN `&0 <= p2 * p3` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= --p2 * --p3 ==> &0 <= p2 * p3`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `p2 < &0` THENL
   [SUBGOAL_THEN `&0 <= (p2 - p1) * p3 /\ &0 <= --p1 * (C - p3)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `&0 <= (p3 - p1) * p2 /\ &0 <= --p1 * (C - p2)` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* Bounds and minima of continuous real functions on compact sets, and     *)
(* restriction of continuity on [a,b) x M to [a,c) x U.                      *)

let RFA_CMAP_COMPACT_BOUND = prove
 (`!(top:A topology) (f:A->real) K.
     continuous_map (top,euclideanreal) f /\ compact_in top K
     ==> ?B. !x. x IN K ==> f x <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_bounded (IMAGE (f:A->real) K)` MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN REWRITE_TAC[real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
    MESON_TAC[REAL_ARITH `abs x <= B ==> x <= B`]]);;

let RFA_CMAP_COMPACT_MIN = prove
 (`!(top:A topology) (f:A->real) K.
     continuous_map (top,euclideanreal) f /\ compact_in top K /\ ~(K = {})
     ==> ?x. x IN K /\ !y. y IN K ==> f x <= f y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (f:A->real) K` REAL_COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; real_compact_def] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN MESON_TAC[]]);;

let RFA_CMAP_RESTRICT_TU = prove
 (`!(top:A topology) (f:real->A->real) a b c U.
     c <= b /\ U SUBSET topspace top /\
     continuous_map
       (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                      (subtopology top (topspace top)),
        euclideanreal) (\z. f (FST z) (SND z))
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < c})
                          (subtopology top U),
            euclideanreal) (\z. f (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM SUBTOPOLOGY_CROSS]) THEN
  REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
  EXISTS_TAC `{t | a <= t /\ t < b} CROSS topspace(top:A topology)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CROSS_MONO THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* Bound of sqrt |Rm|^2 on [a,c] x U for a flow from a, U compact.           *)

let RFA_RMD2_SQRT_BOUND = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b (g:real->A->real^N^N) U c.
     ricci_flow_from (top,atlas) a b g /\ compact_in top U /\ a <= c /\ c < b
     ==> ?C. &0 <= C /\
             !t x. a <= t /\ t <= c /\ x IN U
                   ==> sqrt(rfa_rmd2 0 atlas (g t) x) <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^N^N`] RFA_RMD2_CONTINUOUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                   (subtopology (top:A topology) (topspace top))`;
    `\z:real#A. rfa_rmd2 0 (atlas:((A->bool)#(A->real^N))->bool)
                  ((g:real->A->real^N^N) (FST z)) (SND z)`;
    `real_interval[a,c] CROSS (U:A->bool)`] RFA_CMAP_COMPACT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_IN_CROSS] THEN REPEAT DISJ2_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `max (sqrt B) (&0)` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  REPEAT STRIP_TAC THEN DISJ1_TAC THEN REWRITE_TAC[SQRT_MONO_LE_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* lambda >= delta >= 0 on a compact open set U is preserved along a 3D     *)
(* Ricci flow (weak maximum principle with the Rayleigh barrier).            *)

let RFA_SECMIN_LOWER_PRESERVED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) U delta.
     ricci_flow_from (top,atlas) a b g /\ compact_in top U /\ open_in top U /\
     &0 <= delta /\ (!x. x IN U ==> delta <= mfd_sec_min atlas (g a) x)
     ==> !t x. a <= t /\ t < b /\ x IN U ==> delta <= mfd_sec_min atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `x1:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_from]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN ASM_CASES_TAC `t:real = a` THENL
     [ASM_MESON_TAC[ricci_flow_from];
      UNDISCH_TAC `ricci_flow_on (top,atlas) a b (g:real->A->real^3^3)` THEN
      REWRITE_TAC[ricci_flow_on] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c = (t1 + b) / &2` THEN
  SUBGOAL_THEN `t1 < c /\ c < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `U:A->bool`; `c:real`]
         RFA_RMD2_SQRT_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `a:real`; `c:real`; `g:real->A->real^3^3`;
                 `\t x. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                                    ((g:real->A->real^3^3) t) (x:A)`;
                 `\t:real u:real. &2 * C * min u (&0)`; `\t:real. delta:real`]
         RFA_MINP_BARRIER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* a < c *)
    ASM_REAL_ARITH_TAC;
    (* metrics *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* continuity *)
    MATCH_MP_TAC RFA_CMAP_RESTRICT_TU THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC RFA_SECMIN_CONTINUOUS_GEN THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ricci_flow_from];
    (* Lipschitz *)
    REPEAT STRIP_TAC THEN EXISTS_TAC `&2 * C` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= C ==> abs C = C`; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    (* H' = psi(t,H) *)
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= d ==> min d (&0) = &0`; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    (* the barrier *)
    MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `U:A->bool`; `t0:real`; `x0:A`]
           RFA_SECMIN_BARRIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^3->bool`
      (X_CHOOSE_THEN `phi:real->real^3->real` (X_CHOOSE_THEN `D:real`
       (X_CHOOSE_THEN `p2:real` (X_CHOOSE_THEN `p3:real` STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `W:real^3->bool`; `phi:real->real^3->real`;
                          `D:real`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
     `((\y. lift((phi:real->real^3->real) t0 y)) has_derivative (\v. vec 0))
      (at (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)) x0))`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> l + y <= l + z:real`) THEN
    MATCH_MP_TAC RFA_REACTION_LOWER THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sqrt(rfa_rmd2 0 (atlas:((A->bool)#(A->real^3))->bool)
                     ((g:real->A->real^3^3) t0) x0) <= C`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

