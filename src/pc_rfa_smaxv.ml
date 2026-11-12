(* ========================================================================= *)
(* Unit pc_rfa_smaxv: the strong maximum principle for lambda = mfd_sec_min  *)
(* along a 3D Ricci flow with lambda >= 0 (RFA_SECMIN_STRONG), through upper *)
(* barriers (the Rayleigh barrier in any chart, with its Laplacian identity  *)
(* at every point) in place of a smooth supersolution.                       *)
(* ========================================================================= *)

needs "src/pc_rfa_tmaxp.ml";;
needs "src/pc_rfa_spread.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The Laplacian identity without a critical point, and the                  *)
(* Rayleigh barrier for lambda in an arbitrary chart (RFA_SECMIN_BARRIER_C). *)
(* ========================================================================= *)

(* g(E,E) has zero derivative at y0 (E covariantly constant at y0, g        *)
(* parallel), so the Laplacian identity of the Rayleigh barrier needs no    *)
(* critical point.                                                          *)

let RFA_EXT_DN_METRIC = prove
 (`!U (G:real^N->real^N^N) y0 e h.
     metric_field U G /\ y0 IN U
     ==> frechet_derivative
           (\x. lift(lmetric2 G x (\m. e - christoffel G y0 (x - y0) e))) (at y0) h =
         vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `lmetric2 (G:real^N->real^N^N)`;
                 `y0:real^N`; `e:real^N`; `y0:real^N`; `h:real^N`] RFA_EXT_DN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`] LNABLA_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`; `h:real^N`]
         RFA_VEXT_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(!u. u 1 = vec 0 ==> lmetric2 (G:real^N->real^N^N) y0 u = &0) /\
                (!u. u 2 = vec 0 ==> lmetric2 G y0 u = &0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[lmetric2] THEN SIMP_TAC[DOT_LZERO; MATRIX_VECTOR_MUL_RZERO; DOT_RZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH] THEN REWRITE_TAC[REAL_ADD_LID; LIFT_NUM]);;

let RFA_BARRIER_LAP2 = prove
 (`!U (G:real^N->real^N^N) W y0 e p1 (phi:real^N->real).
     metric_field U G /\ y0 IN U /\ open W /\ y0 IN W /\ W SUBSET U /\
     e dot (G y0 ** e) = &1 /\
     (!v. lpcurv G y0 (\m. if m = 1 then v else e) = p1 * (v dot (G y0 ** e))) /\
     (!y. y IN W ==> ~(e - christoffel G y0 (y - y0) e = vec 0)) /\
     (!y. y IN W
          ==> phi y = lpcurv G y (\m. e - christoffel G y0 (y - y0) e) /
                      lmetric2 G y (\m. e - christoffel G y0 (y - y0) e))
     ==> llap G phi y0 = ltlap 2 G (lpcurv G) y0 (\m. e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field W (G:real^N->real^N^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`;
                 `p1:real`] RFA_ZSHIFT_LAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] RFA_LPCURV_FIELD) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`] LRG_LMETRIC2_FIELD) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `lpcurv (G:real^N->real^N^N)`; `y0:real^N`; `e:real^N`]
         RFA_EXT_EVAL_SMOOTH) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `W:real^N->bool`; `G:real^N->real^N^N`;
                 `lmetric2 (G:real^N->real^N^N)`; `y0:real^N`; `e:real^N`]
         RFA_EXT_EVAL_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!y. y IN W
        ==> &0 < lmetric2 (G:real^N->real^N^N) y
                   (\m. e - christoffel G y0 (y - y0) e)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lmetric2] THEN
    MATCH_MP_TAC LRG_METRIC_POS THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on W (\y. lift((phi:real^N->real) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
    EXISTS_TAC
     `\y. lift(drop(lift(lpcurv (G:real^N->real^N^N) y
                           (\m. e - christoffel G y0 (y - y0) e))) /
               drop(lift(lmetric2 G y (\m. e - christoffel G y0 (y - y0) e))))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_DIV THEN ASM_SIMP_TAC[LIFT_DROP] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real) y0 = p1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(SPEC `e:real^N` (ASSUME
     `!v. lpcurv (G:real^N->real^N^N) y0 (\m. if m = 1 then v else e) =
          p1 * (v dot (G y0 ** e))`)) THEN
    REWRITE_TAC[COND_ID; lmetric2] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `llap (G:real^N->real^N^N)
                (\z. ((phi:real^N->real) z - p1) *
                     lmetric2 G z (\m. e - christoffel G y0 (z - y0) e)) y0` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `&0 < lmetric2 (G:real^N->real^N^N) z (\m. e - christoffel G y0 (z - y0) e)`
    MP_TAC THENL [ASM_SIMP_TAC[]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
    [`W:real^N->bool`; `G:real^N->real^N^N`; `\z:real^N. (phi:real^N->real) z - p1`;
     `\z. lmetric2 (G:real^N->real^N^N) z (\m. e - christoffel G y0 (z - y0) e)`;
     `y0:real^N`] RFA_LLAP_MUL)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y0:real^N`; `e:real^N`]
         RFA_EXT_DN_METRIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[rfa_lginner; rfa_d1; DROP_VEC; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  SUM_0; REAL_ADD_RID] THEN
  REWRITE_TAC[lmetric2] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  MP_TAC(BETA_RULE(ISPECL [`W:real^N->bool`; `G:real^N->real^N^N`; `phi:real^N->real`;
                           `\z:real^N. p1:real`; `y0:real^N`] RFA_LLAP_SUB)) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; RFA_LLAP_CONST; REAL_SUB_RZERO]);;

let RFA_SECMIN_BARRIER_C = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) U c t0 x0.
     ricci_flow_on (top,atlas) a b g /\ open_in top U /\ c IN atlas /\
     a < t0 /\ t0 < b /\ x0 IN FST c /\ x0 IN U
     ==> ?d W (phi:real->real^3->real) D p2 p3.
           &0 < d /\ open W /\ SND c x0 IN W /\
           W SUBSET IMAGE (SND c) (FST c INTER U) /\
           (!y. y IN W ==> mfd_sec_min atlas (g t0) (chart_inv c y) <= phi t0 y) /\
           phi t0 (SND c x0) = mfd_sec_min atlas (g t0) x0 /\
           (!t. t0 - d < t /\ t <= t0 ==> mfd_sec_min atlas (g t) x0 <= phi t (SND c x0)) /\
           smooth_map_on W (\y. lift(phi t0 y)) /\
           ((\t. phi t (SND c x0)) has_real_derivative D)
             (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
           mfd_sec_min atlas (g t0) x0 <= p2 /\ mfd_sec_min atlas (g t0) x0 <= p3 /\
           llap (metric_local atlas c (g t0)) (phi t0) (SND c x0) +
           &2 * (mfd_sec_min atlas (g t0) x0 pow 2 + p2 * p3) = D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)) /\
                (!y. y IN IMAGE (SND c) (FST c INTER U) ==> chart_inv c y IN U)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
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
    (* llap *)
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x + z = y + z:real`) THEN
    MATCH_MP_TAC RFA_BARRIER_LAP2 THEN
    MAP_EVERY EXISTS_TAC
     [`V:real^3->bool`;
      `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                   ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`;
      `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1)`] THEN
    ASM_REWRITE_TAC[lmetric2] THEN SIMP_TAC[IN_ELIM_THM]]);;


(* ========================================================================= *)
(* The spreading lemma in a chart for barrier supersolutions                 *)
(* (RFA_SPREAD_CORE_B, RFA_SPREAD_B).                                        *)
(* ========================================================================= *)

(* The left derivative at a point where f is minimal on the left is <= 0. *)

let RFA_LEFT_MIN_DERIV_WITHIN = prove
 (`!(f:real->real) D t d e.
     (f has_real_derivative D) (atreal t within {s | t - d <= s /\ s <= t}) /\
     &0 < d /\ &0 < e /\
     (!s. t - e < s /\ s < t ==> f t <= f s)
     ==> D <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `D:real`; `t:real`; `{s | t - d <= s /\ s <= t}`;
                 `D / &2`] RFA_LEFT_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `h = min k (min d e) / &2` THEN
  SUBGOAL_THEN `&0 < h /\ h < k /\ h <= d /\ h < e` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) t <= f(t - h)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < h * D` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let RFA_SPREAD_CORE_B = prove
 (`!Om a b (G:real->real^N->real^N^N) (v:real->real^N->real) B y R t1 t2
    dl lam rho2 V k L0 C1.
     lrg_lsmooth Om a b G /\
     (\w. lift(v (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift t1,lift t2] PCROSS cball(y,R)) /\
     a < t1 /\ t1 < t2 /\ t2 < b /\ cball(y,R) SUBSET Om /\ &0 < dl /\ &0 < B /\
     &0 < rho2 /\ &0 <= V /\ rho2 + V * (t2 - t1) = R pow 2 /\ &0 < R /\
     2 <= k /\ &0 < L0 /\
     ((V + C1) / rho2) * L0 * R pow 2 <= &4 * (&k - &1) /\
     B + &2 * &k * ((V + C1) / rho2) <= lam /\
     (!t z x. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
              ==> x dot (G t z ** x) <= L0 * (x dot x)) /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
            ==> abs(llap (G t) (\w. norm(w - y) pow 2) z) <= C1) /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R) ==> &0 <= v t z) /\
     (!t z. t1 < t /\ t <= t2 /\ z IN cball(y,R)
            ==> ?d W (q:real->real^N->real) D.
                  &0 < d /\ open W /\ z IN W /\
                  (!z'. z' IN W ==> v t z' <= q t z') /\ q t z = v t z /\
                  (!s. t - d < s /\ s <= t ==> v s z <= q s z) /\
                  smooth_map_on W (\z'. lift(q t z')) /\
                  ((\s. q s z) has_real_derivative D)
                    (atreal t within {s | t - d <= s /\ s <= t}) /\
                  llap (G t) (q t) z - B * v t z <= D) /\
     (!z. z IN cball(y,R) ==> rfa_sbump dl lam t1 rho2 V k y t1 z <= v t1 z)
     ==> !t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R)
               ==> rfa_sbump dl lam t1 rho2 V k y t z <= v t z`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "lsm vsm at1 t12 t2b cb dlp Bp r2p Vp mR Rp k2 L0p kc lamc qf lb vpos sup init" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  ABBREV_TAC `K = interval[lift t1,lift t2] PCROSS cball(y:real^N,R)` THEN
  ABBREV_TAC `uf = \w:real^(1,N)finite_sum.
                     (v:real->real^N->real) (drop(fstcart w)) (sndcart w) -
                     rfa_sbump dl lam t1 rho2 V k (y:real^N) (drop(fstcart w)) (sndcart w)` THEN
  SUBGOAL_THEN `compact(K:real^(1,N)finite_sum->bool) /\ ~(K = {})` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL] THEN
    REWRITE_TAC[PCROSS_EQ_EMPTY; INTERVAL_EQ_EMPTY_1; CBALL_EQ_EMPTY; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:real^(1,N)finite_sum->bool) SUBSET interval(lift a,lift b) PCROSS Om`
  ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(lift o (uf:real^(1,N)finite_sum->real)) continuous_on K` ASSUME_TAC THENL
   [EXPAND_TAC "uf" THEN REWRITE_TAC[o_DEF; LIFT_SUB] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THENL
     [USE_THEN "vsm" MATCH_ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `{w:real^(1,N)finite_sum | t1 <= drop(fstcart w)}` THEN
      ASM_SIMP_TAC[RFA_SBUMP_CONT] THEN EXPAND_TAC "K" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART] THEN
      REWRITE_TAC[FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`uf:real^(1,N)finite_sum->real`; `K:real^(1,N)finite_sum->bool`]
         CONTINUOUS_ATTAINS_INF) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FORALL_IN_PCROSS; EXISTS_LIFT; FORALL_LIFT;
              IN_INTERVAL_1; LIFT_DROP] THEN
  EXPAND_TAC "uf" THEN REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `ts:real` (X_CHOOSE_THEN `zs:real^N`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))))) THEN
  SUBGOAL_THEN `&0 <= (v:real->real^N->real) ts zs - rfa_sbump dl lam t1 rho2 V k y ts zs`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `ms = rho2 + V * (ts - t1)` THEN
  SUBGOAL_THEN `rho2 <= ms /\ ms <= R pow 2 /\ &0 < ms` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ms" THEN
    SUBGOAL_THEN `&0 <= V * (ts - t1) /\ V * (ts - t1) <= V * (t2 - t1)` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (v:real->real^N->real) ts zs` ASSUME_TAC THENL
   [USE_THEN "vpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(zs - y:real^N) pow 2 < ms` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho2:real`; `V:real`; `k:num`;
                   `y:real^N`; `ts:real`; `zs:real^N`] RFA_SBUMP_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < ts` ASSUME_TAC THENL
   [ASM_CASES_TAC `ts:real = t1` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    USE_THEN "init" (MP_TAC o SPEC `zs:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < ts /\ ts < b` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field Om ((G:real->real^N->real^N^N) ts) /\ (zs:real^N) IN Om`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(zs:real^N) IN ball(y,sqrt ms) /\ ball(y,sqrt ms) SUBSET cball(y,R)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RFA_BALL_SQRT_IFF] THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `z:real^N` THEN
    ASM_SIMP_TAC[RFA_BALL_SQRT_IFF] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sup" (MP_TAC o SPECL [`ts:real`; `zs:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^N->bool`
    (X_CHOOSE_THEN `q:real->real^N->real` (X_CHOOSE_THEN `Dq:real`
      STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `W' = W INTER ball(y:real^N,sqrt ms)` THEN
  SUBGOAL_THEN `open(W':real^N->bool) /\ (zs:real^N) IN W' /\ W' SUBSET ball(y,sqrt ms) /\
                W' SUBSET W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on W' (\z. lift((q:real->real^N->real) ts z)) /\
    smooth_map_on W' (\z. lift(rfa_sbump dl lam t1 rho2 V k (y:real^N) ts z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
     [EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `ball(y:real^N,sqrt ms)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "ms" THEN MATCH_MP_TAC RFA_SBUMP_SMOOTH_BALL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= llap ((G:real->real^N->real^N^N) ts)
            (\z. (q:real->real^N->real) ts z - rfa_sbump dl lam t1 rho2 V k y ts z) zs`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LLAP_LOCAL_MIN THEN
    MAP_EVERY EXISTS_TAC [`Om:real^N->bool`; `W':real^N->bool`] THEN
    BETA_TAC THEN ASM_REWRITE_TAC[LIFT_SUB] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`ts:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real->real^N->real) ts z <= q ts z` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`W':real^N->bool`; `(G:real->real^N->real^N^N) ts`;
                 `(q:real->real^N->real) ts`;
                 `rfa_sbump dl lam t1 rho2 V k (y:real^N) ts`; `zs:real^N`] RFA_LLAP_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
  MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho2:real`; `V:real`; `k:num`;
                 `y:real^N`; `ts:real`; `zs:real^N`] RFA_SBUMP_TDERIV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Dw:real` ASSUME_TAC o MATCH_MP RFA_EX_DERIV) THEN
  SUBGOAL_THEN `Dq - Dw <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LEFT_MIN_DERIV_WITHIN THEN
    EXISTS_TAC `\s. (q:real->real^N->real) s zs - rfa_sbump dl lam t1 rho2 V k y s zs` THEN
    MAP_EVERY EXISTS_TAC [`ts:real`; `d:real`; `min d (ts - t1)`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "min" (MP_TAC o SPECL [`s:real`; `zs:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real->real^N->real) s zs <= q s zs` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(G:real->real^N->real^N^N) ts`; `dl:real`; `lam:real`; `t1:real`;
                 `rho2:real`; `V:real`; `k:num`; `y:real^N`; `ts:real`; `zs:real^N`;
                 `R pow 2`; `L0:real`; `C1:real`; `B:real`; `Dw:real`] RFA_SBUMP_SUBSOL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC RFA_LGRAD2_SQDIST_LOW THEN EXISTS_TAC `Om:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
    USE_THEN "qf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `&0 < B * (rfa_sbump dl lam t1 rho2 V k (y:real^N) ts zs - (v:real->real^N->real) ts zs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


let RFA_SPREAD_B = prove
 (`!Om a b (G:real->real^N->real^N^N) (v:real->real^N->real) B y rho R t1 t2 dl.
     lrg_lsmooth Om a b G /\
     (\w. lift(v (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift t1,lift t2] PCROSS cball(y,R)) /\
     a < t1 /\ t1 < t2 /\ t2 < b /\ &0 < rho /\ rho < R /\ cball(y,R) SUBSET Om /\
     &0 < dl /\
     (!t z. t1 <= t /\ t <= t2 /\ z IN cball(y,R) ==> &0 <= v t z) /\
     (!t z. t1 < t /\ t <= t2 /\ z IN cball(y,R)
            ==> ?d W (q:real->real^N->real) D.
                  &0 < d /\ open W /\ z IN W /\
                  (!z'. z' IN W ==> v t z' <= q t z') /\ q t z = v t z /\
                  (!s. t - d < s /\ s <= t ==> v s z <= q s z) /\
                  smooth_map_on W (\z'. lift(q t z')) /\
                  ((\s. q s z) has_real_derivative D)
                    (atreal t within {s | t - d <= s /\ s <= t}) /\
                  llap (G t) (q t) z - B * v t z <= D) /\
     (!z. z IN ball(y,rho) ==> dl <= v t1 z)
     ==> !z. z IN ball(y,R) ==> &0 < v t2 z`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "lsm vsm at1 t12 t2b rhop rhoR cb dlp vpos sup init" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  ABBREV_TAC `B1 = max B (&1)` THEN
  SUBGOAL_THEN `&0 < B1 /\ B <= B1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. t1 < t /\ t <= t2 /\ z IN cball(y,R)
          ==> ?d W (q:real->real^N->real) D.
                &0 < d /\ open W /\ z IN W /\
                (!z'. z' IN W ==> (v:real->real^N->real) t z' <= q t z') /\
                q t z = v t z /\
                (!s. t - d < s /\ s <= t ==> v s z <= q s z) /\
                smooth_map_on W (\z'. lift(q t z')) /\
                ((\s. q s z) has_real_derivative D)
                  (atreal t within {s | t - d <= s /\ s <= t}) /\
                llap ((G:real->real^N->real^N^N) t) (q t) z - B1 * v t z <= D`
  (LABEL_TAC "sup1") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "sup" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^N->bool`
      (X_CHOOSE_THEN `q:real->real^N->real` (X_CHOOSE_THEN `D:real`
        STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `W:real^N->bool`; `q:real->real^N->real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `B * (v:real->real^N->real) t z <= B1 * v t z` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "vpos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `K = interval[lift t1,lift t2] PCROSS cball(y:real^N,R)` THEN
  SUBGOAL_THEN
   `compact(K:real^(1,N)finite_sum->bool) /\
    K SUBSET interval(lift a,lift b) PCROSS Om /\
    (!t z. pastecart (lift t) z IN K <=> (t1 <= t /\ t <= t2) /\ z IN cball(y,R))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL; COMPACT_CBALL] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `K:real^(1,N)finite_sum->bool`] RFA_LSMOOTH_QFORM_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `\w:real^N. norm(w - y) pow 2`;
                 `K:real^(1,N)finite_sum->bool`] RFA_LSMOOTH_LLAP_BOUND) THEN
  ASM_SIMP_TAC[RFA_SQDIST_SMOOTH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` ASSUME_TAC) THEN
  ABBREV_TAC `V = (R pow 2 - rho pow 2) / (t2 - t1)` THEN
  SUBGOAL_THEN `&0 <= V /\ rho pow 2 + V * (t2 - t1) = R pow 2 /\ &0 < rho pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(t2 - t1 = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_CHOOSE_TAC `n:num`
    (SPEC `((V + C1) / rho pow 2) * L0 * R pow 2 / &4` REAL_ARCH_SIMPLE) THEN
  ABBREV_TAC `k = n + 2` THEN
  SUBGOAL_THEN `2 <= k /\ ((V + C1) / rho pow 2) * L0 * R pow 2 <= &4 * (&k - &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `lam = B1 + &2 * &k * ((V + C1) / rho pow 2)` THEN
  MP_TAC(ISPECL [`Om:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `v:real->real^N->real`; `B1:real`; `y:real^N`; `R:real`; `t1:real`;
                 `t2:real`; `dl:real`; `lam:real`; `rho pow 2`; `V:real`; `k:num`;
                 `L0:real`; `C1:real`] RFA_SPREAD_CORE_B) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(z:real^N) IN ball(y,rho)` THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `dl:real` THEN
        ASM_SIMP_TAC[RFA_SBUMP_INIT; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`dl:real`; `lam:real`; `t1:real`; `rho pow 2`; `V:real`; `k:num`;
                     `y:real^N`; `t1:real`; `z:real^N`] RFA_SBUMP_ZERO) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `~((z:real^N) IN ball(y,rho))` THEN
        REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN USE_THEN "vpos" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "cmp") THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `rfa_sbump dl lam t1 (rho pow 2) V k (y:real^N) t2 z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RFA_SBUMP_POS THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[NORM_POS_LE; ARITH_EQ] THEN
    UNDISCH_TAC `(z:real^N) IN ball(y,R)` THEN
    REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist];
    USE_THEN "cmp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_CBALL] THEN UNDISCH_TAC `(z:real^N) IN ball(y,R)` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* lambda in charts, spreading of its positivity, local                      *)
(* neighbourhoods, and the strong maximum principle (RFA_SECMIN_STRONG).     *)
(* ========================================================================= *)

(* lambda in chart coordinates is continuous on [t1,b) x chart for t1 > a. *)

let RFA_SECMIN_CHART_CONT = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) U phi t1.
     ricci_flow_on (top,atlas) a b g /\ (U,phi) IN atlas /\ a < t1 /\ t1 < b
     ==> (\w. lift(mfd_sec_min atlas (g (drop(fstcart w))) (chart_inv (U,phi) (sndcart w))))
         continuous_on
         {w | t1 <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN IMAGE phi U}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `t1:real`] RFA_RICCI_FLOW_ON_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real`
   (X_CHOOSE_THEN `FF:real^(1,3)finite_sum->real^(3,3)finite_prod` STRIP_ASSUME_TAC)) THEN
  MP_TAC(BETA_RULE(ISPECL
    [`IMAGE (phi:A->real^3) U`; `t1:real`; `b:real`; `e:real`;
     `\t. metric_local atlas (U:A->bool,phi:A->real^3) ((g:real->A->real^3^3) t)`;
     `FF:real^(1,3)finite_sum->real^(3,3)finite_prod`] RFA_LAM_CHART_CONTINUOUS)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^3^3) t)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN
    DISCH_THEN(MP_TAC o SPEC `(U:A->bool,phi:A->real^3)`) THEN
    ASM_REWRITE_TAC[FST; SND];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_LIFT; CONTINUOUS_MAP_EUCLIDEAN; o_DEF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_NEG) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:real^(1,3)finite_sum` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM LIFT_NEG; LIFT_EQ] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) (drop(fstcart(w:real^(1,3)finite_sum)))`;
                 `(U:A->bool,phi:A->real^3)`;
                 `chart_inv (U:A->bool,phi:A->real^3) (sndcart(w:real^(1,3)finite_sum))`]
         RFA_SECMIN_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FST] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SND]);;

(* Spreading of positivity of lambda in a chart (barrier version of       *)
(* RFA_MFD_SPREAD): lambda >= 0, lambda(t1,z0) > 0 ==> lambda(t2,.) > 0 on *)
(* the chart ball of radius R around phi z0.                                *)

let RFA_SECMIN_SPREAD = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3)
    (U:A->bool) (phi:A->real^3) z0 R t1 t2.
     ricci_flow_on (top,atlas) a b g /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     (U,phi) IN atlas /\ z0 IN U /\ &0 < R /\
     cball(phi z0,R) SUBSET IMAGE phi U /\
     a < t1 /\ t1 < t2 /\ t2 < b /\ &0 < mfd_sec_min atlas (g t1) z0
     ==> !x. x IN U /\ phi x IN ball(phi z0,R) ==> &0 < mfd_sec_min atlas (g t2) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 < b:real` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")) THEN
  SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `y0 = (phi:A->real^3) z0` THEN
  ABBREV_TAC `Om = IMAGE (phi:A->real^3) U` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `(U:A->bool,phi:A->real^3)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lrg_lsmooth Om a b (\t. metric_local atlas (U:A->bool,phi:A->real^3) ((g:real->A->real^3^3) t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_LSMOOTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* continuity of lambda in the chart *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`; `t1:real`]
         RFA_SECMIN_CHART_CONT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "vc") THEN
  SUBGOAL_THEN
   `?rho. &0 < rho /\ rho < R /\
          !z. z IN ball(y0,rho)
              ==> mfd_sec_min atlas ((g:real->A->real^3^3) t1) z0 / &2 <=
                  mfd_sec_min atlas (g t1) (chart_inv (U:A->bool,phi:A->real^3) z)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y0:real^3) IN Om` ASSUME_TAC THENL
     [ASM SET_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(\z. lift(mfd_sec_min atlas ((g:real->A->real^3^3) t1)
                  (chart_inv (U:A->bool,phi:A->real^3) z))) continuous at y0`
    MP_TAC THENL
     [SUBGOAL_THEN
       `(\z. lift(mfd_sec_min atlas ((g:real->A->real^3^3) t1)
                    (chart_inv (U:A->bool,phi:A->real^3) z))) continuous_on Om`
      MP_TAC THENL
       [SUBGOAL_THEN
         `(\z. lift(mfd_sec_min atlas ((g:real->A->real^3^3) t1)
                      (chart_inv (U:A->bool,phi:A->real^3) z))) =
          (\w. lift(mfd_sec_min atlas (g (drop(fstcart w)))
                      (chart_inv (U,phi) (sndcart w)))) o
          (\z. pastecart (lift t1) z)`
        SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
          REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
          ALL_TAC] THEN
        FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART;
                    SNDCART_PASTECART; LIFT_DROP] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL];
        ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]];
      ALL_TAC] THEN
    REWRITE_TAC[continuous_at; DIST_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `mfd_sec_min atlas ((g:real->A->real^3^3) t1) z0 / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (R / &2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U:A->bool,phi:A->real^3) y0 = z0` SUBST1_TAC THENL
     [EXPAND_TAC "y0" THEN USE_THEN "ci1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Om:real^3->bool`; `a:real`; `b:real`;
                 `\t. metric_local atlas (U:A->bool,phi:A->real^3) ((g:real->A->real^3^3) t)`;
                 `\t z. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                          ((g:real->A->real^3^3) t) (chart_inv (U:A->bool,phi:A->real^3) z)`;
                 `&1`; `y0:real^3`; `rho:real`; `R:real`; `t1:real`; `t2:real`;
                 `mfd_sec_min atlas ((g:real->A->real^3^3) t1) z0 / &2`] RFA_SPREAD_B) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN REPEAT CONJ_TAC THENL
     [(* continuity on the cylinder *)
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART;
                  SNDCART_PASTECART; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM SET_TAC[];
      (* nonnegativity *)
      MAP_EVERY X_GEN_TAC [`t:real`; `z:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    (* barriers *)
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN Om` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `x = chart_inv (U:A->bool,phi:A->real^3) z` THEN
    SUBGOAL_THEN `(x:A) IN U /\ (phi:A->real^3) x = z` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN USE_THEN "ci2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `U:A->bool`;
                   `(U:A->bool,phi:A->real^3)`; `t:real`; `x:A`] RFA_SECMIN_BARRIER_C) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[FST] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FST; SND; INTER_IDEMPOT] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^3->bool`
      (X_CHOOSE_THEN `q:real->real^3->real` (X_CHOOSE_THEN `D:real`
       (X_CHOOSE_THEN `p2:real` (X_CHOOSE_THEN `p3:real` STRIP_ASSUME_TAC)))))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `W:real^3->bool`; `q:real->real^3->real`; `D:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= mfd_sec_min atlas ((g:real->A->real^3^3) t) x` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= p2 * p3 /\
                  &0 <= mfd_sec_min atlas ((g:real->A->real^3^3) t) x pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:A->real^3) x`) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ci1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:A) IN U`)]));;

let RFA_SECMIN_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) x.
     ricci_flow_on (top,atlas) a b g /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     x IN topspace top
     ==> ?N. open_in top N /\ x IN N /\ N SUBSET topspace top /\
             !z z' t1 t2. z IN N /\ z' IN N /\ a < t1 /\ t1 < t2 /\ t2 < b /\
                          &0 < mfd_sec_min atlas (g t1) z
                          ==> &0 < mfd_sec_min atlas (g t2) z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^3))->bool) x` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?R. &0 < R /\ cball((phi:A->real^3) x,R) SUBSET IMAGE phi U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (phi:A->real^3) U)` THEN REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{z | z IN U /\ (phi:A->real^3) z IN ball(phi x,R / &3)}` THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{z | z IN U /\ (phi:A->real^3) z IN ball(phi x,R / &3)} =
      {z | z IN topspace(subtopology top U) /\
           phi z IN IMAGE phi U INTER ball(phi x,R / &3)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `z:A` THEN
      SUBGOAL_THEN `(U:A->bool) SUBSET topspace top` MP_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:A`) THEN
      MP_TAC(ISPECL [`phi:A->real^3`; `U:A->bool`; `z:A`] FUN_IN_IMAGE) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^3) U)` THEN
    SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CONTINUOUS_MAP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_BALL] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `z':A`; `t1:real`; `t2:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`;
                 `U:A->bool`; `phi:A->real^3`; `z:A`; `&2 * R / &3`; `t1:real`; `t2:real`]
         RFA_SECMIN_SPREAD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball((phi:A->real^3) x,R)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`(phi:A->real^3) x`; `(phi:A->real^3) z`; `w:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN
  MP_TAC(ISPECL [`(phi:A->real^3) z`; `(phi:A->real^3) x`; `(phi:A->real^3) z'`]
         DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`(phi:A->real^3) z`; `(phi:A->real^3) x`] DIST_SYM) THEN
  ASM_REAL_ARITH_TAC);;


let RFA_SECMIN_STRONG = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t0 x0.
     ricci_flow_on (top,atlas) a b g /\ connected_space top /\
     (!t x. a < t /\ t < b /\ x IN topspace top ==> &0 <= mfd_sec_min atlas (g t) x) /\
     a < t0 /\ t0 < b /\ x0 IN topspace top /\ &0 < mfd_sec_min atlas (g t0) x0
     ==> !t x. t0 < t /\ t < b /\ x IN topspace top ==> &0 < mfd_sec_min atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN topspace top
        ==> ?N. open_in top N /\ x IN N /\ N SUBSET topspace top /\
                !z z' t1 t2. z IN N /\ z' IN N /\ a < t1 /\ t1 < t2 /\ t2 < b /\
                             &0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t1) z
                             ==> &0 < mfd_sec_min atlas (g t2) z'`
  (LABEL_TAC "loc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_SECMIN_LOCAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `S = {x:A | x IN topspace top /\
                         !t. t0 < t /\ t < b ==> &0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x}` THEN
  SUBGOAL_THEN
   `!x N. x IN topspace top /\ open_in top N /\ x IN N /\ N SUBSET topspace top /\
          (!z z' t1 t2. z IN N /\ z' IN N /\ a < t1 /\ t1 < t2 /\ t2 < b /\
                        &0 < mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t1) z
                        ==> &0 < mfd_sec_min atlas (g t2) z') /\
          ~(N INTER S = {})
          ==> N SUBSET S`
  (LABEL_TAC "spread") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "nn") MP_TAC))))) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z':A` THEN DISCH_TAC THEN
    UNDISCH_TAC `(z:A) IN S` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "nn" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `(t0 + t) / &2`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x0:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x0:A`; `t0:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (S:A->bool) /\ closed_in top S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:A) IN S` THEN EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "spread" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
     [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:A) IN topspace top`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N:A->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `N INTER (S:A->bool) = {}` THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `N SUBSET (S:A->bool)` MP_TAC THENL
     [USE_THEN "spread" MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `S = topspace top:A->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `connected_space (top:A topology)` THEN
    REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    DISCH_THEN(MP_TAC o SPEC `S:A->bool`) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN S` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;
