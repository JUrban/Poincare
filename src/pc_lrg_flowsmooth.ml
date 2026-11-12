(* ========================================================================= *)
(* pc_lrg_flowsmooth: smooth families of local metrics on an open set U, t   *)
(* in (ta,tb) (lrg_lsmooth), joint smoothness in (t,y) of their derivative,  *)
(* inverse, Christoffel, Riemann, Ricci and scalar terms, and Ricci flows    *)
(* read in an atlas chart are local Ricci flows (LRG_RICCI_FLOW_ON_CHART).   *)
(* The file loads only pc_lrg_evol, pc_rf_basic and pc_mfd_maps;             *)
(* pc_p2a_lgeo1 builds on it.                                                *)
(* ========================================================================= *)

needs "src/pc_lrg_evol.ml";;
needs "src/pc_rf_basic.ml";;
needs "src/pc_mfd_maps.ml";;

prioritize_real();;
type_invention_error := true;;

(* A smooth family of local metrics on U for t in (ta,tb), jointly smooth   *)
(* in (t,y) (the text of p2a_lsmooth of pc_p2a_defs).                        *)

let lrg_lsmooth = new_definition
 `lrg_lsmooth (U:real^N->bool) (ta:real) (tb:real) (Gt:real->real^N->real^N^N) <=>
    open U /\ ta < tb /\
    (!t. ta < t /\ t < tb ==> metric_field U (Gt t)) /\
    smooth_map_on (interval(lift ta,lift tb) PCROSS U)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (Gt (drop(fstcart z)) (sndcart z)))`;;

(* ------------------------------------------------------------------------- *)
(* The Ricci tensor in two charts (the text of MFDR_LRICCI_CHART_TRANS of   *)
(* pc_mfd_restrict, which needs pc_grg_dist; restated here to keep the      *)
(* closure low).                                                             *)
(* ------------------------------------------------------------------------- *)

let LRG_LRICCI_CHART_TRANS = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi (g:A->real^N^N) x u v.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        (U,phi) IN atlas /\ (V,psi) IN atlas /\ x IN U INTER V
        ==> lricci (metric_local atlas (U,phi) g) (phi x) u v =
            lricci (metric_local atlas (V,psi) g) (psi x)
                   (chart_jac (U,phi) (V,psi) x u) (chart_jac (U,phi) (V,psi) x v)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `lricci (mpullback (chart_trans (U:A->bool,phi:A->real^N) (V,psi))
                      (metric_local atlas (V,psi) (g:A->real^N^N)))
           (phi x) u v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_LOCAL THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CHART_OVERLAP_IMAGE_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC METRIC_LOCAL_TRANS THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                `x:A`] CHART_TRANS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (psi:A->real^N) (U INTER V)`; `IMAGE (phi:A->real^N) (U INTER V)`;
    `chart_trans (U:A->bool,phi:A->real^N) (V,psi)`;
    `chart_trans (V:A->bool,psi:A->real^N) (U,phi)`;
    `metric_local atlas (V:A->bool,psi:A->real^N) (g:A->real^N^N)`;
    `(phi:A->real^N) x`; `u:real^N`; `v:real^N`] LRICCI_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC RIEMANNIAN_METRIC_OVERLAP THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `phi:A->real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CHART_TRANS_DIFFEO THEN
      MAP_EVERY EXISTS_TAC
       [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[chart_jac; SND]]);;


(* ------------------------------------------------------------------------- *)
(* A Ricci flow read in an atlas chart is a local Ricci flow on the chart   *)
(* image (the metric in chart c is the congruence of the metric in the      *)
(* preferred chart by the Jacobian of the chart transition).                 *)
(* ------------------------------------------------------------------------- *)

let LRG_CONGR_ENTRY_DERIV = prove
 (`!(G:real->real^N^N) (D:real^N^N) (M:real^N^N) t i j.
     1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N) /\
     (!k l. 1 <= k /\ k <= dimindex(:N) /\ 1 <= l /\ l <= dimindex(:N)
            ==> ((\s. G s$k$l) has_real_derivative D$k$l) (atreal t))
     ==> ((\s. (transp M ** G s ** M)$i$j) has_real_derivative
          (transp M ** D ** M)$i$j) (atreal t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[matrix_mul; transp] THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN ASM_SIMP_TAC[]);;

let LRG_RICCI_FLOW_ON_CHART = prove
 (`!top atlas a b (g:real->A->real^N^N) c.
     ricci_flow_on (top,atlas) a b g /\ c IN atlas
     ==> lricci_flow (IMAGE (SND c) (FST c)) a b (\t. metric_local atlas c (g t))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ricci_flow_on; lricci_flow] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`; `i:num`; `j:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `x = chart_inv (c:(A->bool)#(A->real^N)) y` THEN
  SUBGOAL_THEN `(x:A) IN FST(c:(A->bool)#(A->real^N)) /\ SND c x = y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c' = chart_at (atlas:((A->bool)#(A->real^N))->bool) x` THEN
  SUBGOAL_THEN `(c':(A->bool)#(A->real^N)) IN atlas /\ x IN FST c'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN MATCH_MP_TAC CHART_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `M = matrix(chart_jac (c:(A->bool)#(A->real^N)) c' x)` THEN
  SUBGOAL_THEN
    `!s. metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) s) y =
         transp (M:real^N^N) ** g s x ** M`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                   `(g:real->A->real^N^N) s`; `x:A`] METRIC_LOCAL_JAC) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "M" THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "c'" THEN MATCH_MP_TAC METRIC_LOCAL_AT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `--(&2) * lricci (metric_local atlas (c:(A->bool)#(A->real^N))
                       ((g:real->A->real^N^N) t)) y (basis i) (basis j) =
     (transp (M:real^N^N) **
      ((lambda k l. --(&2) * mfd_ricci_matrix atlas (g t) x$k$l):real^N^N) ** M)$i$j`
    SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LRG_CONGR_ENTRY_DERIV THEN ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  SUBGOAL_THEN `linear(chart_jac (c:(A->bool)#(A->real^N)) c' x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                   `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                   `x:A`] CHART_JAC_LINEAR) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `FST(c:(A->bool)#(A->real^N))`; `SND(c:(A->bool)#(A->real^N))`;
                 `FST(c':(A->bool)#(A->real^N))`; `SND(c':(A->bool)#(A->real^N))`;
                 `(g:real->A->real^N^N) t`; `x:A`; `basis i:real^N`; `basis j:real^N`]
                LRG_LRICCI_CHART_TRANS) THEN
  ASM_SIMP_TAC[PAIR; IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(SND(c':(A->bool)#(A->real^N)) x) IN IMAGE (SND c') (FST c') /\
                metric_field (IMAGE (SND c') (FST c'))
                  (metric_local atlas c' ((g:real->A->real^N^N) t))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[riemannian_metric]]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[MATCH_MP LRG_LRICCI_DOT_FORM (CONJ th
    (ASSUME `(SND(c':(A->bool)#(A->real^N)) x) IN IMAGE (SND c') (FST c')`))]) THEN
  SUBGOAL_THEN
    `((lambda i j. lricci (metric_local atlas (c':(A->bool)#(A->real^N))
                             ((g:real->A->real^N^N) t)) (SND c' x)
                          (basis i) (basis j)):real^N^N) =
     mfd_ricci_matrix atlas (g t) x` SUBST1_TAC THENL
   [EXPAND_TAC "c'" THEN REWRITE_TAC[mfd_ricci_matrix; mfd_ricci]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `matrix(chart_jac (c:(A->bool)#(A->real^N)) c' x) = M`)] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP RFB_CONGRUENCE_DOT th)]) THEN
  ASM_SIMP_TAC[RFB_BASIS_DOT_MATRIX] THEN
  SUBGOAL_THEN
    `((lambda k l. --(&2) * mfd_ricci_matrix atlas ((g:real->A->real^N^N) t) x$k$l)
      :real^N^N) = --(&2) %% mfd_ricci_matrix atlas (g t) x` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; LAMBDA_BETA; MATRIX_CMUL_COMPONENT]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_COMPONENT]);;

(* ========================================================================= *)
(* Joint smoothness in (t,y) for a smooth family of local metrics            *)
(* (lrg_lsmooth; no flow equation needed).  These generalise                 *)
(* LRG_FLOW_MDERIV_SMOOTH and LRG_FLOW_CHRISTOFFEL_SMOOTH of pc_lrg_evol,    *)
(* which assume lricci_flow.                                                 *)
(* ========================================================================= *)

let LRG_LSMOOTH_BASIC = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> open U /\ ta < tb /\
         open(interval(lift ta,lift tb) PCROSS U) /\
         (!t x. pastecart (lift t) x IN interval(lift ta,lift tb) PCROSS U <=>
                ta < t /\ t < tb /\ x IN U) /\
         (!z. z IN interval(lift ta,lift tb) PCROSS U
              ==> ta < drop(fstcart z) /\ drop(fstcart z) < tb /\ sndcart z IN U) /\
         (!t. ta < t /\ t < tb ==> metric_field U (G t)) /\
         smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (G (drop(fstcart z)) (sndcart z)))`,
  REWRITE_TAC[lrg_lsmooth; MESON[PASTECART_FST_SND; PASTECART_IN_PCROSS]
   `!(s:real^1->bool) (t:real^N->bool) z. z IN s PCROSS t <=> fstcart z IN s /\ sndcart z IN t`;
              IN_INTERVAL_1; LIFT_DROP;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN
  REWRITE_TAC[CONJ_ACI]);;

let LRG_JOINT_PARTIAL = prove
 (`!W (f:real^(1,N)finite_sum->real^P) w.
     open W /\ smooth_map_on W f
     ==> smooth_map_on W
           (\z. frechet_derivative (\x. f(pastecart (fstcart z) x)) (at (sndcart z)) w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. frechet_derivative (f:real^(1,N)finite_sum->real^P) (at z)
                                     (pastecart (vec 0) w)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^(1,N)finite_sum->real^P`; `fstcart(z:real^(1,N)finite_sum)`;
                 `sndcart(z:real^(1,N)finite_sum)`; `w:real^N`] LRG_SLICE_DERIV) THEN
  REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `W:real^(1,N)finite_sum->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let LRG_LSMOOTH_MDERIV = prove
 (`!U ta tb (G:real->real^N->real^N^N) w.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (mderiv (G (drop(fstcart z))) (sndcart z) w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `\z. frechet_derivative
          (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
               ((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z)))
          (at z) (pastecart (vec 0) w)` THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:real->real^N->real^N^N`; `fstcart(z:real^(1,N)finite_sum)`;
                 `sndcart(z:real^(1,N)finite_sum)`; `w:real^N`]
         LRG_FLOW_MDERIV_JOINT) THEN
  REWRITE_TAC[PASTECART_FST_SND] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift ta,lift tb) PCROSS (U:real^N->bool)` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTORIZE_MATRIFY]]);;

let LRG_LSMOOTH_MDERIV_ENTRY = prove
 (`!U ta tb (G:real->real^N->real^N^N) w v c k.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift((mderiv (G (drop(fstcart z))) (sndcart z) w ** v)$k)) /\
         smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(c dot (mderiv (G (drop(fstcart z))) (sndcart z) w ** v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `w:real^N` o MATCH_MP LRG_LSMOOTH_MDERIV) THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z. lift((mderiv ((G:real->real^N->real^N^N) (drop(fstcart z)))
                       (sndcart z) w ** v)$k)) =
      (\m:real^(N,N)finite_prod. lift(((matrify m:real^N^N) ** v)$k)) o
      (\z. vectorize(mderiv (G (drop(fstcart z))) (sndcart z) w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_MUL_COMPONENT];
    SUBGOAL_THEN
     `(\z. lift(c dot (mderiv ((G:real->real^N->real^N^N) (drop(fstcart z)))
                              (sndcart z) w ** v))) =
      (\m:real^(N,N)finite_prod. lift(c dot ((matrify m:real^N^N) ** v))) o
      (\z. vectorize(mderiv (G (drop(fstcart z))) (sndcart z) w))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT]]);;

let LRG_LSMOOTH_GINV = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           ((vectorize:real^N^N->real^(N,N)finite_prod) o
            (\z. matrix_inv(G (drop(fstcart z)) (sndcart z))))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MATCH_MP_TAC LRG_SMOOTH_MATRIX_INV THEN ASM_REWRITE_TAC[o_DEF] THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop(fstcart(z:real^(1,N)finite_sum)))`;
                 `sndcart(z:real^(1,N)finite_sum)`] LRG_METRIC_INVERTIBLE) THEN
  ASM_SIMP_TAC[]);;

let LRG_LSMOOTH_CHRISTOFFEL = prove
 (`!U ta tb (G:real->real^N->real^N^N) u v.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. christoffel (G (drop(fstcart z))) (sndcart z) u v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[christoffel] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATVEC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LSMOOTH_GINV) THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE
    (ASSUME `open(interval(lift ta,lift tb) PCROSS (U:real^N->bool))`)] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_SUB] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[LRG_LSMOOTH_MDERIV_ENTRY];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_SIMP_TAC[LRG_LSMOOTH_MDERIV_ENTRY]]);;

let LRG_SMOOTH_LINEAR_ARG = prove
 (`!W (L:real^M->real^N->real^P) (X:real^M->real^N).
     open W /\ (!z. z IN W ==> linear(L z)) /\
     (!j. 1 <= j /\ j <= dimindex(:N) ==> smooth_map_on W (\z. L z (basis j))) /\
     smooth_map_on W X
     ==> smooth_map_on W (\z. L z (X z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z. vsum (1..dimindex(:N))
                    (\j. drop(lift((X:real^M->real^N) z$j)) %
                         (L:real^M->real^N->real^P) z (basis j))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    SUBGOAL_THEN `linear((L:real^M->real^N->real^P) z)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL];
    MATCH_MP_TAC SMOOTH_MAP_ON_VSUM_OPEN THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_LIFT_COMPONENT]]);;

let LRG_LSMOOTH_AT = prove
 (`!U ta tb (G:real->real^N->real^N^N) z.
     lrg_lsmooth U ta tb G /\ z IN interval(lift ta,lift tb) PCROSS U
     ==> metric_field U (G (drop(fstcart z))) /\ sndcart z IN U`,
  MESON_TAC[LRG_LSMOOTH_BASIC]);;

let LRG_LSMOOTH_DCHRISTOFFEL = prove
 (`!U ta tb (G:real->real^N->real^N^N) u v w.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. frechet_derivative (\x. christoffel (G (drop(fstcart z))) x v w)
                                   (at (sndcart z)) u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                                  (sndcart z) v w`;
                 `u:real^N`] LRG_JOINT_PARTIAL) THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL; FSTCART_PASTECART; SNDCART_PASTECART]);;

let LRG_LSMOOTH_CHRISTOFFEL_ARG = prove
 (`!U ta tb (G:real->real^N->real^N^N) u (X:real^(1,N)finite_sum->real^N).
     lrg_lsmooth U ta tb G /\
     smooth_map_on (interval(lift ta,lift tb) PCROSS U) X
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. christoffel (G (drop(fstcart z))) (sndcart z) u (X z)) /\
         smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. christoffel (G (drop(fstcart z))) (sndcart z) (X z) u)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THENL
   [MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                   `\z. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                                    (sndcart z) u`;
                   `X:real^(1,N)finite_sum->real^N`] LRG_SMOOTH_LINEAR_ARG);
    MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                   `\z w. christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                                      (sndcart z) w u`;
                   `X:real^(1,N)finite_sum->real^N`] LRG_SMOOTH_LINEAR_ARG)] THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `z:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `(G:real->real^N->real^N^N) (drop(fstcart(z:real^(1,N)finite_sum)))`;
                 `sndcart(z:real^(1,N)finite_sum)`] LRG_CHRISTOFFEL_LINEAR) THEN
  ASM_MESON_TAC[LRG_LSMOOTH_AT; ETA_AX]);;

let LRG_LSMOOTH_CHRISTOFFEL2 = prove
 (`!U ta tb (G:real->real^N->real^N^N) a b c.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. christoffel (G (drop(fstcart z))) (sndcart z) a
                  (christoffel (G (drop(fstcart z))) (sndcart z) b c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `ta:real`; `tb:real`; `G:real->real^N->real^N^N`;
                 `a:real^N`;
                 `\z:real^(1,N)finite_sum.
                    christoffel ((G:real->real^N->real^N^N) (drop(fstcart z)))
                                (sndcart z) b c`] LRG_LSMOOTH_CHRISTOFFEL_ARG) THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL]);;

let LRG_LSMOOTH_LRIEMANN = prove
 (`!U ta tb (G:real->real^N->real^N^N) u v w.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lriemann (G (drop(fstcart z))) (sndcart z) u v w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lriemann] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_CHRISTOFFEL2; LRG_LSMOOTH_DCHRISTOFFEL]);;

let LRG_SMOOTH_LIFT_MUL = prove
 (`!s (f:real^M->real) g.
     open s /\ smooth_map_on s (\x. lift(f x)) /\ smooth_map_on s (\x. lift(g x))
     ==> smooth_map_on s (\x. lift(f x * g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(f x)`; `\x:real^M. lift(g x)`]
                SMOOTH_MAP_ON_MUL_LIFT_OPEN) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let LRG_SMOOTH_LIFT_SUM = prove
 (`!s (f:num->real^M->real) k.
     open s /\ FINITE k /\ (!i. i IN k ==> smooth_map_on s (\x. lift(f i x)))
     ==> smooth_map_on s (\x. lift(sum k (\i. f i x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\i x. lift((f:num->real^M->real) i x)`;
                 `k:num->bool`] SMOOTH_MAP_ON_LIFT_SUM) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX]);;

let LRG_LSMOOTH_LRICCI = prove
 (`!U ta tb (G:real->real^N->real^N^N) v w.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lricci (G (drop(fstcart z))) (sndcart z) v w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lricci] THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`interval(lift ta,lift tb) PCROSS (U:real^N->bool)`;
                 `\z. lriemann ((G:real->real^N->real^N^N) (drop(fstcart z)))
                               (sndcart z) (basis k) v w`; `k:num`]
                SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_LRIEMANN]);;

let LRG_LSMOOTH_GINV_ENTRY = prove
 (`!U ta tb (G:real->real^N->real^N^N) i j.
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(matrix_inv(G (drop(fstcart z)) (sndcart z))$i$j))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LRG_LSMOOTH_GINV) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. lift(matrix_inv((G:real->real^N->real^N^N) (drop(fstcart z)) (sndcart z))$i$j)) =
    (\m:real^(N,N)finite_prod. lift((matrify m:real^N^N)$i$j)) o
    ((vectorize:real^N^N->real^(N,N)finite_prod) o
     (\z. matrix_inv(G (drop(fstcart z)) (sndcart z))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; MATRIFY_ADD; MATRIFY_CMUL; MATRIX_ADD_COMPONENT;
              MATRIX_CMUL_COMPONENT; LIFT_ADD; LIFT_CMUL]);;

let LRG_LSMOOTH_LSCALAR = prove
 (`!U ta tb (G:real->real^N->real^N^N).
     lrg_lsmooth U ta tb G
     ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
           (\z. lift(lscalar (G (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
  REWRITE_TAC[lscalar] THEN MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_SUM THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL THEN
  ASM_SIMP_TAC[LRG_LSMOOTH_GINV_ENTRY; LRG_LSMOOTH_LRICCI]);;


