(* ========================================================================= *)
(* pc_pde_rdt_energy: the Ricci-DeTurck existence, part 4.  Energy estimates *)
(* on the manifold, in the chart-wise norms pde_mnorm2, for solutions of the *)
(* frozen linear problem d/dt v = tr_g Hess_h v + f with constants depending *)
(* only on bounds of g and of the background h.                              *)
(* ========================================================================= *)

needs "src/pc_pde_rdt_coef.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A cutoff of the manifold in a chart, and the time derivative              *)
(* of a cut-off chart representative of a solution of pde_mlin_sol.          *)
(* ------------------------------------------------------------------------- *)

let RDT_CUTOFF_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) K.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) K)
     ==> smooth_map_on (IMAGE (SND c) (FST c)) (\z. lift(phi(chart_inv c z))) /\
         (!z. z IN IMAGE (SND c) (FST c) /\ ~(z IN K) ==> lift(phi(chart_inv c z)) = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `K:real^N->bool`]
    PDE_ME_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `\z. lift(if z IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
                         then (phi:A->real)(chart_inv c z) else &0)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ASM_SIMP_TAC[LIFT_NUM]]);;

(* The time derivative of a cut-off chart representative of a solution.     *)

let RDT_CHART_TDERIV = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 v (c:(A->bool)#(A->real^N)) (phi:A->real)
    K t z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\
     mfd_smooth atlas (\x. lift(phi x)) /\ compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) K) /\
     a < t /\ t < b /\ z IN IMAGE (SND c) (FST c)
     ==> partial_derivative 1
           (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (phi(chart_inv c (sndcart w)) %%
                   metric_local atlas c (v(drop(fstcart w))) (sndcart w)))
           (pastecart (lift t) z) =
         phi(chart_inv c z) %
         (pde_lop0 (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t)
                   (\y. vectorize(metric_local atlas c (v t) y)) z +
          vectorize(metric_local atlas c (f t) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pde_mlin_sol]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `K:real^N->bool`;
                 `v:real->A->real^N^N`; `a:real`; `b:real`] PDM_TFAM_PIECE_UPTO) THEN
  ASM_REWRITE_TAC[pde_upto; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `F1:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open (S:real^(1,N)finite_sum->bool) /\ pastecart (lift t) z IN S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN S
        ==> (vectorize:real^N^N->real^(N,N)finite_prod)
              (phi(chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %%
               metric_local atlas c ((v:real->A->real^N^N) (drop(fstcart w))) (sndcart w)) =
            F1 w`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`[1]`; `S:real^(1,N)finite_sum->bool`;
    `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
           (phi(chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %%
            metric_local atlas c ((v:real->A->real^N^N) (drop(fstcart w))) (sndcart w))`;
    `F1:real^(1,N)finite_sum->real^(N,N)finite_prod`; `pastecart (lift t) (z:real^N)`]
    TEXT_ITERATED_PARTIAL_LOCAL_AT) THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[iterated_partial] THEN DISCH_THEN SUBST1_TAC THEN
  (* the derivative of the extension in time *)
  SUBGOAL_THEN `(F1:real^(1,N)finite_sum->real^(N,N)finite_prod)
                differentiable (at (pastecart (lift t) z))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (:real^N)` THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                 LIFT_DROP; IN_UNIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`F1:real^(1,N)finite_sum->real^(N,N)finite_prod`; `t:real`; `z:real^N`]
    PDE_ST_TIME_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                 `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `t:real`; `z:real^N`] PDE_ML_SOL_CHART_LOP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z)` o
             MATCH_MP HAS_VECTOR_DERIVATIVE_CMUL) THEN
  REWRITE_TAC[PDE_LOP_LOP0] THEN DISCH_TAC THEN
  MATCH_MP_TAC VECTOR_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\r. (F1:real^(1,N)finite_sum->real^(N,N)finite_prod) (pastecart r z)` THEN
  EXISTS_TAC `lift t` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
  EXISTS_TAC `\s. (phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %
                  (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas c ((v:real->A->real^N^N) (drop s)) z)` THEN
  EXISTS_TAC `interval(lift a,lift b)` THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL_1; LIFT_DROP] THEN
  X_GEN_TAC `r:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (r:real^1) (z:real^N)`) THEN
  EXPAND_TAC "S" THEN
  ASM_REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[LIFT_DROP; VECTORIZE_CMUL] THEN ASM_SIMP_TAC[]);;

(* The time derivative of the cut-off representative in pde_lop0 form, with *)
(* the forcing and the commutator with the cutoff of a larger cutoff theta. *)

let RDT_CHART_TD_SPLIT = prove
 (`!top atlas a b (k:real->A->real^N^N) h f v0 v (c:(A->bool)#(A->real^N)) (phi:A->real)
    (theta:A->real) K O t z.
     smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
     (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
     pde_mlin_sol (top,atlas) a b k h f v0 v /\
     mfd_smooth atlas (\x. lift(phi x)) /\ compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) K) /\
     open O /\ K SUBSET O /\ O SUBSET IMAGE (SND c) (FST c) /\
     (!z. z IN O ==> theta(chart_inv c z) = &1) /\
     a < t /\ t < b /\ z IN IMAGE (SND c) (FST c)
     ==> partial_derivative 1
           (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (phi(chart_inv c (sndcart w)) %%
                   metric_local atlas c (v(drop(fstcart w))) (sndcart w)))
           (pastecart (lift t) z) =
         pde_lop0 (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t)
                  (\y. vectorize(phi(chart_inv c y) %% metric_local atlas c (v t) y)) z +
         (phi(chart_inv c z) % vectorize(metric_local atlas c (f t) z) -
          pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
                      (\y. lift(phi(chart_inv c y)))
                      (\y. vectorize(theta(chart_inv c y) %% metric_local atlas c (v t) y)) z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                 `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                 `phi:A->real`; `K:real^N->bool`; `t:real`; `z:real^N`] RDT_CHART_TDERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN `open(U:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `K:real^N->bool`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                                       (metric_local atlas (c:(A->bool)#(A->real^N))
                                          ((v:real->A->real^N^N) t) y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `v:real->A->real^N^N`; `t:real`] PDE_ML_TFAM_SLICE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[pde_mlin_sol; REAL_LT_IMP_LE]; ALL_TAC] THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[mfd_tensor2_smooth; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `pde_mlaa atlas (c:(A->bool)#(A->real^N)) k t`;
                 `pde_mlbt atlas (c:(A->bool)#(A->real^N)) k h t`;
                 `pde_mlct atlas (c:(A->bool)#(A->real^N)) k h t`;
                 `\y. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y))`;
                 `\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas (c:(A->bool)#(A->real^N))
                           ((v:real->A->real^N^N) t) y)`; `z:real^N`] PDE_MT_LOP0_CUTOFF) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o REWRITE_RULE[GSYM VECTORIZE_CMUL]) THEN
  SUBGOAL_THEN
   `pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
      (\y. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) y)))
      (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas c ((v:real->A->real^N^N) t) y)) z =
    pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
      (\y. lift(phi(chart_inv c y)))
      (\y. vectorize((theta:A->real)(chart_inv c y) %% metric_local atlas c (v t) y)) z`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `(z:real^N) IN O` THENL
     [MATCH_MP_TAC PDE_ME_COMM_LOCAL THEN EXISTS_TAC `O:real^N->bool` THEN
      ASM_SIMP_TAC[MATRIX_CMUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^N) IN K)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `a = vec 0 /\ b = vec 0 ==> a:real^(N,N)finite_prod = b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
    EXISTS_TAC `U DIFF (K:real^N->bool)` THEN
    ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chart Sobolev norm of a difference.                                       *)
(* ------------------------------------------------------------------------- *)

let RDT_NORM_SUB_SQ = prove
 (`!(a:real^N) b. norm(a - b) pow 2 <= &2 * norm a pow 2 + &2 * norm b pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(a:real^N) + norm(b:real^N)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE; NORM_TRIANGLE_SUB] THEN
    CONV_TAC NORM_ARITH;
    MP_TAC(SPEC `norm(a:real^N) - norm(b:real^N)` REAL_LE_POW_2) THEN REAL_ARITH_TAC]);;

let RDT_HS_SUB2 = prove
 (`!U K (f:real^N->real^Q) g m.
     open U /\ compact K /\ K SUBSET U /\ smooth_map_on U f /\ smooth_map_on U g /\
     (!y. y IN U /\ ~(y IN K) ==> f y = vec 0 /\ g y = vec 0)
     ==> rdt_hs U m (\y. f y - g y) <= &2 * rdt_hs U m f + &2 * rdt_hs U m g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN U /\ ~(y IN K) ==> (f:real^N->real^Q) y = vec 0) /\
                (!y. y IN U /\ ~(y IN K) ==> (g:real^N->real^Q) y = vec 0)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rdt_hs] THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD; PDE_INDEX_LISTS_FINITE] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `rdt_cs U K (\y. norm(iterated_partial l (f:real^N->real^Q) y) pow 2) /\
    rdt_cs U K (\y. norm(iterated_partial l (g:real^N->real^Q) y) pow 2)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RDT_CS_SQNORM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\y. norm(iterated_partial l (f:real^N->real^Q) y) pow 2`; `&2`] RDT_INT_CMUL) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\y. norm(iterated_partial l (g:real^N->real^Q) y) pow 2`; `&2`] RDT_INT_CMUL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`;
                 `\y. &2 * norm(iterated_partial l (f:real^N->real^Q) y) pow 2`;
                 `\y. &2 * norm(iterated_partial l (g:real^N->real^Q) y) pow 2`] RDT_INT_ADD) THEN
  ASM_SIMP_TAC[RDT_CS_CMUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RDT_INT_LE THEN EXISTS_TAC `K:real^N->bool` THEN
  ASM_SIMP_TAC[RDT_CS_CMUL; RDT_CS_ADD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_CS_SQNORM THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_SUB_OPEN] THEN
    ASM_SIMP_TAC[VECTOR_SUB_RZERO];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`l:num list`; `U:real^N->bool`; `f:real^N->real^Q`; `g:real^N->real^Q`]
      TEXT_ITERATED_PARTIAL_SUB_OPEN) THEN
    ASM_SIMP_TAC[RDT_NORM_SUB_SQ]]);;

(* ------------------------------------------------------------------------- *)
(* The energy of one chart.  The time derivative of the chart                *)
(* norm of the cut-off representative u = phi V of a solution is bounded by *)
(* C (|u|_s^2 + |phi F|_(s-1)^2 + |theta V|_s^2), with C depending only on   *)
(* the compact sets and the bounds of the coefficients (RDT_CHART_ENERGY for *)
(* d/dt u = L u + phi F - [L,phi] (theta V), RDT_COMM_HS for the commutator).*)
(* ------------------------------------------------------------------------- *)

let RDT_MCHART = prove
 (`!(K:real^N->bool) KT s lam M Qb Ap.
     compact K /\ compact KT /\ 2 * dimindex(:N) + 4 <= s /\ &0 < lam /\ &0 <= M /\
     &0 <= Qb /\ &0 <= Ap
     ==> ?C. &0 <= C /\
             !top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) (theta:A->real) O a b
              (k:real->A->real^N^N) h f v0 v t.
               smooth_manifold_atlas top atlas /\ c IN atlas /\ riemannian_metric atlas h /\
               (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
               pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
               pde_mlin_sol (top,atlas) a b k h f v0 v /\ a < t /\ t < b /\
               mfd_smooth atlas (\x. lift(phi x)) /\ K SUBSET IMAGE (SND c) (FST c) /\
               (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) K) /\
               mfd_smooth atlas (\x. lift(theta x)) /\ KT SUBSET IMAGE (SND c) (FST c) /\
               (!x. ~(theta x = &0) ==> x IN IMAGE (chart_inv c) KT) /\
               open O /\ K SUBSET O /\ O SUBSET IMAGE (SND c) (FST c) /\
               (!z. z IN O ==> theta(chart_inv c z) = &1) /\
               (!y. y IN K ==> pde_jetn (s + 1) (\z. lift(phi(chart_inv c z))) y <= Ap) /\
               (!y w. y IN K ==> lam * norm w pow 2 <= w dot (pde_mlaa atlas c k t y ** w)) /\
               (!y. y IN K ==> rdt_cjet (s DIV 2 + 1) (pde_mlaa atlas c k t)
                                        (pde_mlbt atlas c k h t) (pde_mlct atlas c k h t) y
                               <= M) /\
               drop(integral K (\y. lift(rdt_cjet s (pde_mlaa atlas c k t)
                                                  (pde_mlbt atlas c k h t)
                                                  (pde_mlct atlas c k h t) y pow 2))) <= Qb
               ==> sum (pde_index_lists s (:N))
                     (\l. drop(integral (IMAGE (SND c) (FST c))
                       (\z. lift(&2 *
                          (iterated_partial l
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (phi(chart_inv c z) %% metric_local atlas c (v t) z)) z dot
                           iterated_partial l
                             (\z. partial_derivative 1
                                    (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                           (phi(chart_inv c (sndcart w)) %%
                                            metric_local atlas c (v(drop(fstcart w))) (sndcart w)))
                                    (pastecart (lift t) z)) z)))))
                   <= C * (rdt_hs (IMAGE (SND c) (FST c)) s
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (phi(chart_inv c z) %% metric_local atlas c (v t) z)) +
                           rdt_hs (IMAGE (SND c) (FST c)) (s - 1)
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (phi(chart_inv c z) %% metric_local atlas c (f t) z)) +
                           rdt_hs (IMAGE (SND c) (FST c)) s
                             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (theta(chart_inv c z) %% metric_local atlas c (v t) z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `s:num`; `lam:real`; `M:real`; `Qb:real`]
    (INST_TYPE [`:(N,N)finite_prod`,`:Q`] RDT_CHART_ENERGY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CE:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce"))) THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `KT:real^N->bool`; `s:num`; `M:real`; `Qb:real`; `Ap:real`]
    (INST_TYPE [`:(N,N)finite_prod`,`:Q`] RDT_COMM_HS)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CM:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cm"))) THEN
  EXISTS_TAC `CE * (&3 + &2 * CM)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) /\ a < b /\ a <= t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `K:real^N->bool`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `theta:A->real`; `KT:real^N->bool`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t) /\
                mfd_tensor2_smooth atlas ((f:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_MESON_TAC[pde_mlin_sol];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND c) (FST c))
      (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) y)) /\
    smooth_map_on (IMAGE (SND c) (FST c))
      (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas (c:(A->bool)#(A->real^N)) ((f:real->A->real^N^N) t) y))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `mfd_tensor2_smooth atlas ((v:real->A->real^N^N) t)`;
      UNDISCH_TAC `mfd_tensor2_smooth atlas ((f:real->A->real^N^N) t)`] THEN
    REWRITE_TAC[mfd_tensor2_smooth; o_DEF] THEN
    DISCH_THEN(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                 `k:real->A->real^N^N`; `h:A->real^N^N`; `c:(A->bool)#(A->real^N)`]
    PDE_MT_CHART_COEFF_UPTO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `smooth_map_on (IMAGE (SND c) (FST c))
      (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
             (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t x)) /\
    (!i. smooth_map_on (IMAGE (SND c) (FST c))
           (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlbt atlas c k (h:A->real^N^N) t x i))) /\
    smooth_map_on (IMAGE (SND c) (FST c))
      (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                      ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
             (pde_mlct atlas c k h t x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `\t z. (vectorize:real^N^N->real^(N,N)finite_prod)
                              (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                        (k:real->A->real^N^N) t z)`;
                     `t:real`] PDE_ML_UPTO_SLICE_OPEN);
      GEN_TAC THEN
      MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                       ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                              (pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                                        (h:A->real^N^N) t z i)`;
                     `t:real`] PDE_ML_UPTO_SLICE_OPEN);
      MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                     `\t z. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                       ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                              (pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                                        (h:A->real^N^N) t z)`;
                     `t:real`] PDE_ML_UPTO_SLICE_OPEN)] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the cut-off pieces *)
  ABBREV_TAC `U = IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
  SUBGOAL_THEN
   `!(g:real->A->real^N^N) (cut:A->real) KC.
      smooth_map_on U (\z. lift(cut(chart_inv (c:(A->bool)#(A->real^N)) z))) /\
      (!z. z IN U /\ ~(z IN KC) ==> lift(cut(chart_inv c z)) = vec 0) /\
      smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                             (metric_local atlas c (g t) y))
      ==> smooth_map_on U (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 (cut(chart_inv c z) %% metric_local atlas c (g t) z)) /\
          (!z. z IN U /\ ~(z IN KC)
               ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                     (cut(chart_inv c z) %% metric_local atlas c (g t) z) = vec 0)`
  (LABEL_TAC "piece") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[VECTORIZE_CMUL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`U:real^N->bool`;
                     `\z. lift((cut:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))`;
                     `\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                            (metric_local atlas (c:(A->bool)#(A->real^N))
                               ((g:real->A->real^N^N) t) y)`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\ K SUBSET U /\ KT SUBSET U /\ O SUBSET U`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U (\z. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))) /\
    (!z. z IN U /\ ~(z IN K) ==> lift(phi(chart_inv c z)) = vec 0) /\
    smooth_map_on U (\z. lift((theta:A->real)(chart_inv c z))) /\
    (!z. z IN U /\ ~(z IN KT) ==> lift(theta(chart_inv c z)) = vec 0) /\
    smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas c ((v:real->A->real^N^N) t) y)) /\
    smooth_map_on U (\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas c ((f:real->A->real^N^N) t) y)) /\
    smooth_map_on U (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
                           (pde_mlaa atlas c (k:real->A->real^N^N) t x)) /\
    (!i. smooth_map_on U
           (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlbt atlas c k (h:A->real^N^N) t x i))) /\
    smooth_map_on U
      (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                      ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
             (pde_mlct atlas c k h t x))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "piece" (MP_TAC o SPECL [`v:real->A->real^N^N`; `phi:A->real`; `K:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "piece" (MP_TAC o SPECL [`f:real->A->real^N^N`; `phi:A->real`; `K:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "piece" (MP_TAC o SPECL [`v:real->A->real^N^N`; `theta:A->real`; `KT:real^N->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REMOVE_THEN "piece" (K ALL_TAC) THEN
  (* the cut-off pieces and the forcing of the cut-off equation *)
  ABBREV_TAC `p = \z. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))` THEN
  ABBREV_TAC `W = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((theta:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                         metric_local atlas c ((v:real->A->real^N^N) t) z)` THEN
  ABBREV_TAC `u = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                         metric_local atlas c ((v:real->A->real^N^N) t) z)` THEN
  ABBREV_TAC `pF = \z. (vectorize:real^N^N->real^(N,N)finite_prod)
                         ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z) %%
                          metric_local atlas c ((f:real->A->real^N^N) t) z)` THEN
  SUBGOAL_THEN
   `smooth_map_on U (u:real^N->real^(N,N)finite_prod) /\
    (!z. z IN U /\ ~(z IN K) ==> u z = vec 0) /\
    smooth_map_on U (pF:real^N->real^(N,N)finite_prod) /\
    (!z. z IN U /\ ~(z IN K) ==> pF z = vec 0) /\
    smooth_map_on U (W:real^N->real^(N,N)finite_prod) /\
    (!z. z IN U /\ ~(z IN KT) ==> W z = vec 0) /\
    smooth_map_on U (p:real^N->real^1) /\ (!z. z IN U /\ ~(z IN K) ==> p z = vec 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["u"; "pF"; "W"; "p"] THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on U
      (pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
                   (pde_mlbt atlas c k (h:A->real^N^N) t)
                   (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod)) /\
    (!z. z IN U /\ ~(z IN K)
         ==> pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t) p W z = vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[RDT_COMM_LOP0_FUN] THEN
      MP_TAC(ISPECL [`U:real^N->bool`;
                     `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t`;
                     `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N)
                               (h:A->real^N^N) t`; `p:real^N->real^1`]
        RDT_COMM_COEFF_SMOOTH) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC RDT_LOP0_SMOOTH THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC PDE_MT_COMM_ZERO_OPEN THEN
      EXISTS_TAC `U DIFF (K:real^N->bool)` THEN
      ASM_SIMP_TAC[OPEN_DIFF; COMPACT_IMP_CLOSED; IN_DIFF]];
    ALL_TAC] THEN
  (* the time derivative on the chart in pde_lop0 form *)
  SUBGOAL_THEN
   `!z. z IN U
        ==> partial_derivative 1
              (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %%
                      metric_local atlas c ((v:real->A->real^N^N) (drop(fstcart w)))
                        (sndcart w)))
              (pastecart (lift t) z) =
            pde_lop0 (pde_mlaa atlas c (k:real->A->real^N^N) t)
                     (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t)
                     (u:real^N->real^(N,N)finite_prod) z +
            ((pF:real^N->real^(N,N)finite_prod) z -
             pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
                         (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `a:real`; `b:real`;
                   `k:real->A->real^N^N`; `h:A->real^N^N`; `f:real->A->real^N^N`;
                   `v0:A->real^N^N`; `v:real->A->real^N^N`; `c:(A->bool)#(A->real^N)`;
                   `phi:A->real`; `theta:A->real`; `K:real^N->bool`; `O:real^N->bool`;
                   `t:real`; `z:real^N`] RDT_CHART_TD_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXPAND_TAC ["u"; "pF"; "p"; "W"] THEN
    REWRITE_TAC[VECTORIZE_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (pde_index_lists s (:N))
      (\l. drop(integral U
         (\z. lift(&2 *
            (iterated_partial l (u:real^N->real^(N,N)finite_prod) z dot
             iterated_partial l
               (\z. partial_derivative 1
                      (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                             ((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) (sndcart w)) %%
                              metric_local atlas c ((v:real->A->real^N^N) (drop(fstcart w)))
                                (sndcart w)))
                      (pastecart (lift t) z)) z))))) =
    sum (pde_index_lists s (:N))
      (\l. rdt_int U
         (\z. &2 *
            (iterated_partial l u z dot
             iterated_partial l
               (\y. pde_lop0 (pde_mlaa atlas c (k:real->A->real^N^N) t)
                             (pde_mlbt atlas c k (h:A->real^N^N) t) (pde_mlct atlas c k h t)
                             u y +
                    ((pF:real^N->real^(N,N)finite_prod) y -
                     pde_mt_comm (pde_mlaa atlas c k t) (pde_mlbt atlas c k h t)
                                 (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) y)) z)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    REWRITE_TAC[rdt_int] THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the chart energy *)
  USE_THEN "ce" (MP_TAC o SPECL
   [`U:real^N->bool`; `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t`;
    `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `u:real^N->real^(N,N)finite_prod`;
    `\z. (pF:real^N->real^(N,N)finite_prod) z -
         pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
                     (pde_mlbt atlas c k (h:A->real^N^N) t)
                     (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) z`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX];
      ASM_SIMP_TAC[VECTOR_SUB_RZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->bool`; `pF:real^N->real^(N,N)finite_prod`;
                 `pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t)
                              (pde_mlbt atlas c k (h:A->real^N^N) t)
                              (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod)`;
                 `s - 1`] RDT_HS_SUB2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "cm" (MP_TAC o SPECL
   [`U:real^N->bool`; `pde_mlaa atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) t`;
    `pde_mlbt atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `pde_mlct atlas (c:(A->bool)#(A->real^N)) (k:real->A->real^N^N) (h:A->real^N^N) t`;
    `p:real^N->real^1`; `W:real^N->real^(N,N)finite_prod`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= rdt_hs U (s + 1) (u:real^N->real^(N,N)finite_prod) /\
    &0 <= rdt_hs U s u /\ &0 <= rdt_hs U (s - 1) (pF:real^N->real^(N,N)finite_prod) /\
    &0 <= rdt_hs U s (W:real^N->real^(N,N)finite_prod)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC RDT_HS_POS THENL
     [EXISTS_TAC `K:real^N->bool`; EXISTS_TAC `K:real^N->bool`; EXISTS_TAC `K:real^N->bool`;
      EXISTS_TAC `KT:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `H1 = rdt_hs U (s + 1) (u:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `H0 = rdt_hs U s (u:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `HF = rdt_hs U (s - 1) (pF:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `HW = rdt_hs U s (W:real^N->real^(N,N)finite_prod)` THEN
  ABBREV_TAC `HC = rdt_hs U (s - 1)
                    (pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                           (k:real->A->real^N^N) t)
                                 (pde_mlbt atlas c k (h:A->real^N^N) t)
                                 (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod))` THEN
  ABBREV_TAC `HO = rdt_hs U (s - 1)
                    (\z. (pF:real^N->real^(N,N)finite_prod) z -
                         pde_mt_comm (pde_mlaa atlas (c:(A->bool)#(A->real^N))
                                               (k:real->A->real^N^N) t)
                                     (pde_mlbt atlas c k (h:A->real^N^N) t)
                                     (p:real^N->real^1) (W:real^N->real^(N,N)finite_prod) z)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `CE * HO <= CE * (&2 * HF + &2 * (CM * HW))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`HO <= &2 * HF + &2 * HC`; `HC <= CM * HW`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lam / &2 * H1 /\ &0 <= CE * CM * HW /\ &0 <= CE * HF /\ &0 <= CE * H0 /\
                &0 <= CE * HW /\ &0 <= CE * CM * H0 /\ &0 <= CE * CM * HF`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN RDT_NN_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `--(lam / &2) * H1 + CE * (H0 + HO)` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The energy inequality at level s on the manifold:                         *)
(*   d/dt |v(t)|_s^2 <= C (|v(t)|_s^2 + |f(t)|_(s-1)^2)                       *)
(* for solutions of the frozen problem, C depending only on the cover data,  *)
(* s, the ellipticity constant and the coefficient bounds on the pieces.     *)
(* ------------------------------------------------------------------------- *)

let RDT_COVER_FACTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi.
     smooth_manifold_atlas top atlas /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
     ==> !i. i < n0
             ==> cs i IN atlas /\ compact(ks i) /\ ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
                 mfd_smooth atlas (\x. lift(psi i x)) /\ open(IMAGE (SND(cs i)) (FST(cs i))) /\
                 (!x. ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
    ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
    mfd_smooth atlas (\x. lift((psi:num->A->real) i x))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
    UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
    REWRITE_TAC[pde_cover; pde_cutoffs] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ASM_MESON_TAC[]]);;

(* The per-chart data: a cutoff theta_i equal to 1 near the piece, its      *)
(* localization constant at level m, and the jet bound of the cutoff psi_i. *)

let RDT_CHART_DATA = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi m p.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
     ==> ?TH KT OO DD AP.
           !i. i < n0
               ==> mfd_smooth atlas (\x. lift(TH i x)) /\ compact(KT i) /\
                   KT i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
                   (!x. ~(TH i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (KT i)) /\
                   open(OO i) /\ ks i SUBSET OO i /\ OO i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
                   (!z. z IN OO i ==> TH i (chart_inv (cs i) z) = &1) /\
                   &0 <= DD i /\
                   (!w. pde_tensor_smooth atlas w
                        ==> rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) m
                              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                     (TH i (chart_inv (cs i) z) %%
                                      metric_local atlas (cs i) w z)) <=
                            DD i * pde_mnorm2 atlas n0 cs psi m w) /\
                   &0 <= AP i /\
                   (!y. y IN ks i
                        ==> pde_jetn p (\z. lift(psi i (chart_inv (cs i) z))) y <= AP i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REMOVE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(ks:num->real^N->bool) i`]
    PDE_ME_THETA_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `theta:A->real` (X_CHOOSE_THEN `kt:real^N->bool`
    (X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`theta:A->real`; `kt:real^N->bool`; `O:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `theta:A->real`; `kt:real^N->bool`;
                 `m:num`] PDM_MNORM_LOCALIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `D0:real`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`;
                 `(ks:num->real^N->bool) i`;
                 `\z. lift((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z))`;
                 `p:num`] RDT_JETS_BOUNDED_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `A0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`max D0 (&0)`; `A0:real`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  X_GEN_TAC `w:A->real^N^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:A->real^N^N`) THEN ASM_REWRITE_TAC[rdt_hs; rdt_int] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
  MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[]);;

let RDT_MENERGY_S = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s lam M Qb.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ &0 < lam /\ &0 <= M /\ &0 <= Qb
     ==> ?C. &0 <= C /\
             !a b k h f v0 v t.
               riemannian_metric atlas h /\
               (!t. a <= t /\ t < b ==> riemannian_metric atlas (k t)) /\
               pde_tfam_from atlas a b k /\ pde_tfam_from atlas a b f /\
               pde_mlin_sol (top,atlas) a b k h f v0 v /\ a < t /\ t < b /\
               (!i y w. i < n0 /\ y IN ks i
                        ==> lam * norm w pow 2 <= w dot (pde_mlaa atlas (cs i) k t y ** w)) /\
               (!i y. i < n0 /\ y IN ks i
                      ==> rdt_cjet (s DIV 2 + 1) (pde_mlaa atlas (cs i) k t)
                                   (pde_mlbt atlas (cs i) k h t) (pde_mlct atlas (cs i) k h t) y
                          <= M) /\
               (!i. i < n0
                    ==> drop(integral (ks i)
                          (\y. lift(rdt_cjet s (pde_mlaa atlas (cs i) k t)
                                          (pde_mlbt atlas (cs i) k h t)
                                          (pde_mlct atlas (cs i) k h t) y pow 2))) <= Qb)
               ==> ?D. ((\r. pde_mnorm2 atlas n0 cs psi s (v r)) has_real_derivative D)
                       (atreal t) /\
                       D <= C * (pde_mnorm2 atlas n0 cs psi s (v t) +
                                 pde_mnorm2 atlas n0 cs psi (s - 1) (f t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `s + 1`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
    (GEN `i:num` (ISPECL [`(ks:num->real^N->bool) i`; `(KT:num->real^N->bool) i`; `s:num`;
                          `lam:real`; `M:real`; `Qb:real`; `(AP:num->real) i`] RDT_MCHART))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CC:num->real` (LABEL_TAC "cc")) THEN
  SUBGOAL_THEN `!i. i < n0 ==> &0 <= (CC:num->real) i /\ &0 <= (DD:num->real) i`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "cc" (MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `CS = sum {i | i < n0} (CC:num->real)` THEN
  ABBREV_TAC `DS = sum {i | i < n0} (DD:num->real)` THEN
  SUBGOAL_THEN `&0 <= CS /\ &0 <= DS` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["CS"; "DS"] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n0 ==> (CC:num->real) i <= CS /\ (DD:num->real) i <= DS`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["CS"; "DS"] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[SUM_SING] (ISPECL [`{i:num}`; `{i:num | i < n0}`]
      SUM_SUBSET_SIMPLE)) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM; SING_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `CS * (&1 + &n0 * DS)` THEN CONJ_TAC THENL [RDT_NN_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N) /\
                pde_tensor_smooth atlas ((v:real->A->real^N^N) t) /\
                pde_tensor_smooth atlas ((f:real->A->real^N^N) t)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PDM_TENSOR_SMOOTH_EQ] THEN
    SUBGOAL_THEN `pde_tfam_from atlas a b (v:real->A->real^N^N)` ASSUME_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pde_mlin_sol]); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC PDE_ML_TFAM_SLICE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `a:real`; `b:real`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `v:real->A->real^N^N`; `a:real`; `b:real`; `s:num`] PDM_MNORM2_TFAM_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> EXISTS_TAC (rand(rator(concl th))) THEN REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `&0 <= pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t) /\
    &0 <= pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {i | i < n0}
      (\i. CS * (rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) +
                 rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) (s - 1)
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (psi i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((f:real->A->real^N^N) t) z)) +
                 DS * pde_mnorm2 atlas n0 cs psi s (v t)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cc" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
      `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`; `(TH:num->A->real) i`;
      `(OO:num->real^N->bool) i`; `a:real`; `b:real`; `k:real->A->real^N^N`;
      `h:A->real^N^N`; `f:real->A->real^N^N`; `v0:A->real^N^N`; `v:real->A->real^N^N`;
      `t:real`] o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(v:real->A->real^N^N) t` o check (fun th ->
      can (find_term ((=) `pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool`))
          (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `&0 <= rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     ((psi:num->A->real) i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) /\
      &0 <= rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) (s - 1)
              (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                     (psi i (chart_inv (cs i) z) %%
                      metric_local atlas (cs i) ((f:real->A->real^N^N) t) z))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[rdt_hs; rdt_int] THEN
      CONJ_TAC THEN
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                     `(ks:num->real^N->bool) i`] PDE_ME_CNORM_POS) THEN
      ASM_REWRITE_TAC[pde_me_cnorm; rdt_hs; rdt_int] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(CC:num->real) i <= CS /\ (DD:num->real) i <= DS /\
                  &0 <= CC i /\ &0 <= DD i` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t)` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(CC:num->real) i *
                (rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((psi:num->A->real) i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) +
                 rdt_hs (IMAGE (SND(cs i)) (FST(cs i))) (s - 1)
                   (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (psi i (chart_inv (cs i) z) %%
                           metric_local atlas (cs i) ((f:real->A->real^N^N) t) z)) +
                 DS * E)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `c <= d ==> a + b + c <= a + b + d`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(DD:num->real) i * E` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) s
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (v t) z))) /\
    pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) t) =
    sum {i | i < n0}
      (\i. rdt_hs (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))) (s - 1)
             (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                    ((psi:num->A->real) i (chart_inv (cs i) z) %%
                     metric_local atlas (cs i) (f t) z)))`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [REWRITE_TAC[pde_mnorm2; rdt_hs; rdt_int]; ALL_TAC] THEN
  SIMP_TAC[SUM_LMUL; SUM_ADD; FINITE_NUMSEG_LT; SUM_CONST; CARD_NUMSEG_LT] THEN
  POP_ASSUM(fun th1 -> POP_ASSUM(fun th2 -> REWRITE_TAC[GSYM th1; GSYM th2])) THEN
  ABBREV_TAC `E = pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) t)` THEN
  ABBREV_TAC `EF = pde_mnorm2 atlas n0 cs psi (s - 1) ((f:real->A->real^N^N) t)` THEN
  SUBGOAL_THEN `&0 <= CS * &n0 * DS * EF` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* Gronwall for a differential inequality with a constant forcing bound, on  *)
(* [a,T].                                                                    *)
(* ------------------------------------------------------------------------- *)

let RDT_SHIFT_DERIV = prove
 (`!(Y:real->real) D a t.
     (Y has_real_derivative D) (atreal (t + a))
     ==> ((\r. Y(r + a) - Y a) has_real_derivative D) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r:real. r + a`; `Y:real->real`; `&1`; `D:real`; `t:real`]
    REAL_DIFF_CHAIN_ATREAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`\r:real. r`; `&1`; `\r:real. a:real`; `&0`; `atreal t`]
      HAS_REAL_DERIVATIVE_ADD) THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST; REAL_ADD_RID];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF; REAL_MUL_RID] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\r. (Y:real->real)(r + a)`; `D:real`; `\r:real. (Y:real->real) a`; `&0`;
                 `atreal t`] HAS_REAL_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO]);;

let RDT_GRONWALL_CONST = prove
 (`!(Y:real->real) D a Tm C CF.
     &0 <= C /\ a <= Tm /\ Y real_continuous_on real_interval[a,Tm] /\
     (!t. a < t /\ t < Tm ==> (Y has_real_derivative D t) (atreal t) /\
                            D t <= C * (Y t + CF)) /\
     &0 <= Y a + CF
     ==> !t. a <= t /\ t <= Tm
             ==> Y t <= Y a + (t - a) * (C * (Y a + CF)) * exp(C * (t - a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (Y:real->real)(r + a) - Y a`; `\r. (D:real->real)(r + a)`;
                 `\r:real. &0`; `\r:real. C * (Y(a:real) + CF)`; `C:real`; `C:real`;
                 `Tm - a:real`] PDE_GRONWALL_W) THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_RID; REAL_CONTINUOUS_ON_CONST] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
      MP_TAC(ISPECL [`Y:real->real`; `a:real`; `Tm:real`] PDE_ME_SHIFT_CONT) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r + a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_SIMP_TAC[RDT_SHIFT_DERIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN DISCH_TAC THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - a:real`) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_ADD; REAL_INTEGRAL_0; REAL_ADD_RID] THEN
  SUBGOAL_THEN `real_integral (real_interval[&0,t - a]) (\r. exp(--(C * r)) * C * (Y(a:real) + CF))
                <= (t - a) * (C * (Y a + CF))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,t - a]) (\r:real. C * (Y(a:real) + CF))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      REWRITE_TAC[REAL_INTEGRABLE_CONST; IN_REAL_INTERVAL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
        SUBGOAL_THEN `(\r. exp(--(C * r))) = exp o (\r. --(C * r))` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[REAL_CONTINUOUS_ON_NEG; REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID;
                 REAL_CONTINUOUS_ON_EXP];
        X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * C` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM REAL_EXP_0] THEN REWRITE_TAC[REAL_EXP_MONO_LE] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= &0`) THEN MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      SUBGOAL_THEN `&0 <= t - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `exp(--(C * (t - a))) * (Y t - Y(a:real)) <= (t - a) * (C * (Y a + CF))` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < exp(C * (t - a))` ASSUME_TAC THENL [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ (MATCH_MP REAL_LT_IMP_LE
    (ASSUME `&0 < exp(C * (t - a))`))) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_EXP_ADD; REAL_ADD_RINV; REAL_EXP_0; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Elementary bounds used to pass from the ball to the coefficient bounds:   *)
(* ellipticity of the inverse metric, the norm of the inverse, pointwise     *)
(* bounds from pde_cbound, pointwise jets by Sobolev, the L^2 bound over     *)
(* a piece of a function bounded by a top jet, and the smoothness of the     *)
(* coefficients of tr_G Hess_H for a single metric.                          *)
(* ------------------------------------------------------------------------- *)

let RDT_INV_LOWER = prove
 (`!K (G:real^N^N).
     &0 < K /\ norm(vectorize G) <= K /\ (!w. norm w pow 2 <= K * (w dot (G ** w)))
     ==> !w. inv(K pow 3) * norm w pow 2 <= w dot (transp(matrix_inv G) ** w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:real^N` THEN
  SUBGOAL_THEN `invertible(G:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
    MP_TAC(ISPECL [`K:real`; `(vectorize:real^N^N->real^(N,N)finite_prod) G`] RDT_POSB_INV) THEN
    ASM_REWRITE_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  ABBREV_TAC `u = matrix_inv(G:real^N^N) ** w` THEN
  SUBGOAL_THEN `(G:real^N^N) ** u = w` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `norm(w:real^N) <= K * norm(u:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^N^N`; `u:real^N`] COMPATIBLE_NORM_VECTORIZE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(u:real^N) pow 2 <= K * (u dot w)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(w:real^N) pow 2 <= K pow 3 * (u dot w)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(K * norm(u:real^N)) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[REAL_POW_MUL; REAL_ARITH `K pow 3 * x = K pow 2 * (K * x)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(K pow 3) * (K pow 3 * ((u:real^N) dot w))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL]]);;

let RDT_INV_BOUND = prove
 (`!B (H:real^N^N).
     &0 <= B /\ (!w. norm w pow 2 <= B * (w dot (H ** w)))
     ==> norm(vectorize(matrix_inv H)) <= &(dimindex(:N) * dimindex(:N)) * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `invertible(H:real^N^N)` ASSUME_TAC THENL
   [REWRITE_TAC[INVERTIBLE_DET_NZ] THEN
    MP_TAC(ISPECL [`B:real`; `(vectorize:real^N^N->real^(N,N)finite_prod) H`] RDT_POSB_INV) THEN
    ASM_REWRITE_TAC[MATRIFY_VECTORIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. norm(matrix_inv(H:real^N^N) ** w) <= B * norm(w:real^N)` ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN
    ABBREV_TAC `u = matrix_inv(H:real^N^N) ** w` THEN
    SUBGOAL_THEN `(H:real^N^N) ** u = w` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u:real^N`; `w:real^N`] NORM_CAUCHY_SCHWARZ) THEN DISCH_TAC THEN
    ASM_CASES_TAC `u:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[NORM_0] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(u:real^N)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `norm(u:real^N)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * ((u:real^N) dot w)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_POW_2];
      REWRITE_TAC[REAL_ARITH `n * (B * m) = B * (n * m)`] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC PDE_NORM_VECTORIZE_LE THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(matrix_inv(H:real^N^N) ** basis j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((matrix_inv(H:real^N^N) ** basis j)$i)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; MATRIX_VECTOR_MUL_COMPONENT; DOT_BASIS; REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B * norm(basis j:real^N)` THEN
    ASM_SIMP_TAC[NORM_BASIS; REAL_MUL_RID; REAL_LE_REFL]]);;

let RDT_CBOUND_PT = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) n0 cs ks m B g i y.
     pde_cbound atlas n0 cs ks m B g /\ i < n0 /\ y IN ks i
     ==> norm((vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas (cs i) g y))
         <= B /\
         (!w. norm w pow 2 <= B * (w dot (metric_local atlas (cs i) g y ** w))) /\
         pde_jetn m ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) g) y
         <= &(CARD(pde_index_lists m (:N))) * B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pde_cbound] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`[]:num list`; `y:real^N`]) THEN
    ASM_REWRITE_TAC[PDE_INDEX_LISTS_NIL; iterated_partial; o_THM];
    REWRITE_TAC[pde_jetn] THEN MATCH_MP_TAC SUM_BOUND THEN
    ASM_SIMP_TAC[PDE_INDEX_LISTS_FINITE]]);;

let RDT_SQRT_LE_1ADD = prove
 (`!x. &0 <= x ==> sqrt x <= &1 + x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC);;

let RDT_SOB_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi p.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))
     ==> ?CJ. &0 <= CJ /\
              !(v:A->real^N^N) E i y.
                pde_tensor_smooth atlas v /\
                pde_mnorm2 atlas n0 cs psi (p + dimindex(:N)) v <= E /\
                i < n0 /\ y IN ks i
                ==> pde_jetn p ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                metric_local atlas (cs i) v) y <= CJ * (&1 + E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `p:num`] PDE_MNORM_SOBOLEV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "sob")) THEN
  ABBREV_TAC `c = max C (&0)` THEN
  SUBGOAL_THEN `&0 <= c /\ C <= c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `&(CARD(pde_index_lists p (:N))) * (&1 + c)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
                  ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= pde_mnorm2 atlas n0 cs psi (p + dimindex(:N)) (v:A->real^N^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_ME_MNORM2_POS THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `ks:num->real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E /\ &0 <= c * E` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `(vectorize:real^N^N->real^(N,N)finite_prod) o
                           metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) v`;
                 `y:real^N`; `c * E:real`] PDM_JETN_SQ_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:num list` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C * pde_mnorm2 atlas n0 cs psi (p + dimindex(:N)) (v:A->real^N^N)` THEN
    CONJ_TAC THENL [USE_THEN "sob" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c * pde_mnorm2 atlas n0 cs psi (p + dimindex(:N)) (v:A->real^N^N)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + c * E` THEN
  ASM_SIMP_TAC[RDT_SQRT_LE_1ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= c /\ &0 <= E ==> &1 + c * E <= (&1 + c) * (&1 + E)`) THEN
  ASM_REWRITE_TAC[]);;

(* The L^2 bound over a compact piece of a function dominated by a top jet. *)

let RDT_INTK_TOPJET = prove
 (`!U K KW (W:real^N->real^Q) (Qf:real^N->real) C2 s.
     open U /\ compact K /\ K SUBSET U /\ compact KW /\ KW SUBSET U /\ smooth_map_on U W /\
     (!y. y IN U /\ ~(y IN KW) ==> W y = vec 0) /\
     (\y. lift(Qf y)) continuous_on K /\ &0 <= C2 /\
     (!y. y IN K ==> abs(Qf y) <= C2 * (&1 + pde_jetn s W y))
     ==> drop(integral K (\y. lift(Qf y pow 2))) <=
         &2 * C2 pow 2 * (drop(integral K (\y. lift(&1))) +
                          &(CARD(pde_index_lists s (:N))) * rdt_hs U s W)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. lift(pde_jetn s (W:real^N->real^Q) y)) continuous_on K` ASSUME_TAC THENL
   [MATCH_MP_TAC RDT_JETN_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. lift(pde_jetn s (W:real^N->real^Q) y pow 2)) continuous_on K /\
                (\y. lift((Qf:real^N->real) y pow 2)) continuous_on K /\
                (\y:real^N. lift(&1)) continuous_on K`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONTINUOUS_ON_CONST] THEN CONJ_TAC THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral K (\y. lift(&2 * C2 pow 2 * &1 +
                                     &2 * C2 pow 2 * pde_jetn s (W:real^N->real^Q) y pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      CONJ_TAC THEN REPEAT(MATCH_MP_TAC CONTINUOUS_ON_CMUL) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
      ALL_TAC] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `abs:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:num`; `W:real^N->real^Q`; `y:real^N`] PDE_JETN_POS) THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C2 * (&1 + pde_jetn s (W:real^N->real^Q) y)) pow 2` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C2 * (&1 + pde_jetn s (W:real^N->real^Q) y)` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `C2 * (&1 - pde_jetn s (W:real^N->real^Q) y)` REAL_LE_POW_2) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y:real^N. &2 * C2 pow 2 * &1`;
                 `\y. &2 * C2 pow 2 * pde_jetn s (W:real^N->real^Q) y pow 2`] RDT_INTK_ADD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; LIFT_CMUL] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_CMUL) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y:real^N. &1`; `&2 * C2 pow 2`] RDT_INTK_CMUL) THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y. pde_jetn s (W:real^N->real^Q) y pow 2`;
                 `&2 * C2 pow 2`] RDT_INTK_CMUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
                  ALL_TAC] THEN
  MATCH_MP_TAC RDT_INTK_JETN_SQ THEN EXISTS_TAC `KW:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let RDT_INTK_ONE_POS = prove
 (`!K:real^N->bool. compact K ==> &0 <= drop(integral K (\y. lift(&1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:real^N->bool`; `\y:real^N. &0`; `\y:real^N. &1`] RDT_INTK_LE) THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; LIFT_NUM; INTEGRAL_0; DROP_VEC] THEN
  REWRITE_TAC[REAL_POS]);;

let RDT_TERM_LE_SUM = prove
 (`!(f:num->real) n0 i.
     (!j. j < n0 ==> &0 <= f j) /\ i < n0 ==> f i <= sum {j | j < n0} f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[SUM_SING] (ISPECL [`{i:num}`; `{j:num | j < n0}`]
    SUM_SUBSET_SIMPLE)) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_DIFF; IN_ELIM_THM; SING_SUBSET]);;

(* Smoothness of the coefficients of tr_G Hess_H for one metric G.          *)

let RDT_COEF_SMOOTH = prove
 (`!U (G:real^N->real^N^N) H.
     metric_field U G /\ metric_field U H
     ==> smooth_map_on U (\x. (vectorize:real^N^N->real^(N,N)finite_prod)
                                (transp(matrix_inv(G x)))) /\
         (!c. smooth_map_on U
                (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                                ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                       (pde_mlbb G H x c))) /\
         smooth_map_on U
           (\x. (vectorize:real^(N,N)finite_prod^(N,N)finite_prod
                           ->real^((N,N)finite_prod,(N,N)finite_prod)finite_prod)
                  (pde_mlcc G H x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\ (!z. z IN U ==> ~(det((G:real^N->real^N^N) z) = &0))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[metric_field; LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (rdt_kc (G:real^N->real^N^N) H)` ASSUME_TAC THENL
   [REWRITE_TAC[RDT_KC_FUN] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `metric_field U (G:real^N->real^N^N)` THEN SIMP_TAC[metric_field; o_DEF];
      MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[RDT_GV_SMOOTH; RDT_GDV_SMOOTH]];
    ALL_TAC] THEN
  ABBREV_TAC `S = {x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum |
                   ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}` THEN
  SUBGOAL_THEN `open(S:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum->bool) /\
                IMAGE (rdt_kc (G:real^N->real^N^N) H) U SUBSET S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[LINEAR_FSTCART];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[rdt_kc; FSTCART_PASTECART; MATRIFY_VECTORIZE]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `rdt_phia o rdt_kc (G:real^N->real^N^N) H` THEN
    ASM_REWRITE_TAC[o_THM; RDT_PHIA_KC] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `S:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum->bool` THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[RDT_PHIA_SMOOTH];
    GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `rdt_phib c o rdt_kc (G:real^N->real^N^N) H` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RDT_PHIB_KC]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `S:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum->bool` THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[RDT_PHIB_SMOOTH];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `rdt_phic o rdt_kc (G:real^N->real^N^N) H` THEN
    ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RDT_PHIC_KC]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `S:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                     (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum->bool` THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[RDT_PHIC_SMOOTH]]);;

(* ------------------------------------------------------------------------- *)
(* The coefficient bounds of RDT_MENERGY_S from the ball.  For               *)
(* g with pde_cbound 0 K and |g|_s^2 <= K, and a background h with           *)
(* pde_cbound m B (m >= s + 3): ellipticity inv(K^3), the low jets of the     *)
(* coefficients bounded by M, their top jets bounded in L^2 by Qb.           *)
(* ------------------------------------------------------------------------- *)

let RDT_PIECE = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (phi:A->real) K (v:A->real^N^N).
     smooth_manifold_atlas top atlas /\ c IN atlas /\ mfd_smooth atlas (\x. lift(phi x)) /\
     compact K /\ K SUBSET IMAGE (SND c) (FST c) /\
     (!x. ~(phi x = &0) ==> x IN IMAGE (chart_inv c) K) /\
     smooth_map_on (IMAGE (SND c) (FST c))
       ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c v)
     ==> smooth_map_on (IMAGE (SND c) (FST c))
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (phi(chart_inv c z) %% metric_local atlas c v z)) /\
         (!z. z IN IMAGE (SND c) (FST c) /\ ~(z IN K)
              ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                    (phi(chart_inv c z) %% metric_local atlas c v z) = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`; `phi:A->real`; `K:real^N->bool`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PDM_CHART_OPEN_C]; ALL_TAC] THEN
  REWRITE_TAC[VECTORIZE_CMUL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                   `\z. lift((phi:A->real)(chart_inv (c:(A->bool)#(A->real^N)) z))`;
                   `\y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas (c:(A->bool)#(A->real^N)) (v:A->real^N^N) y)`]
      SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `smooth_map_on (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c))
                   ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas c v)` THEN
    REWRITE_TAC[o_DEF];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LZERO]]);;

let RDT_DIV2 = prove
 (`!s. s DIV 2 * 2 <= s /\ s <= s DIV 2 * 2 + 1`,
  GEN_TAC THEN MP_TAC(SPECL [`s:num`; `2`] DIVISION) THEN ARITH_TAC);;

let RDT_BALL_COEF = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ s + 3 <= m /\ &0 <= B /\ &0 < K
     ==> ?lam M Qb. &0 < lam /\ &0 <= M /\ &0 <= Qb /\
           !h g. riemannian_metric atlas h /\ pde_cbound atlas n0 cs ks m B h /\
                 riemannian_metric atlas g /\ pde_cbound atlas n0 cs ks 0 K g /\
                 pde_mnorm2 atlas n0 cs psi s g <= K
                 ==> (!i y w. i < n0 /\ y IN ks i
                              ==> lam * norm w pow 2 <=
                                  w dot (transp(matrix_inv(metric_local atlas (cs i) g y)) ** w)) /\
                     (!i y. i < n0 /\ y IN ks i
                            ==> rdt_cjet (s DIV 2 + 1)
                                  (\y. transp(matrix_inv(metric_local atlas (cs i) g y)))
                                  (\y c. pde_mlbb (metric_local atlas (cs i) g)
                                                  (metric_local atlas (cs i) h) y c)
                                  (\y. pde_mlcc (metric_local atlas (cs i) g)
                                                (metric_local atlas (cs i) h) y) y <= M) /\
                     (!i. i < n0
                          ==> drop(integral (ks i)
                                (\y. lift(rdt_cjet s
                                  (\y. transp(matrix_inv(metric_local atlas (cs i) g y)))
                                  (\y c. pde_mlbb (metric_local atlas (cs i) g)
                                                  (metric_local atlas (cs i) h) y c)
                                  (\y. pde_mlcc (metric_local atlas (cs i) g)
                                                (metric_local atlas (cs i) h) y) y pow 2)))
                              <= Qb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `s:num`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s - dimindex(:N)`] RDT_SOB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s - dimindex(:N) + dimindex(:N) = s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  ABBREV_TAC `MJ = CJ * (&1 + K)` THEN
  ABBREV_TAC `BH = &(CARD(pde_index_lists m (:N))) * B` THEN
  ABBREV_TAC `LH = &(dimindex(:N) * dimindex(:N)) * B` THEN
  SUBGOAL_THEN `&0 <= MJ /\ &0 <= BH /\ &0 <= LH` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["MJ"; "BH"; "LH"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s DIV 2 + 1) DIV 2 + 1 <= s - dimindex(:N) /\ s DIV 2 + 1 <= s - dimindex(:N) /\
                (s DIV 2 + 1) + 3 <= m`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `s:num` RDT_DIV2) THEN MP_TAC(SPEC `s DIV 2 + 1` RDT_DIV2) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s DIV 2 + 1`; `K:real`; `MJ:real`; `BH:real`; `LH:real`] RDT_COEF_CJET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))) THEN
  MP_TAC(SPECL [`s:num`; `K:real`; `MJ:real`; `BH:real`; `LH:real`] RDT_COEF_CJET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c2"))) THEN
  SUBGOAL_THEN
   `!i. i < n0
        ==> &0 <= &2 * C2 pow 2 *
                  (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
                   &(CARD(pde_index_lists s (:N))) * (DD:num->real) i * K)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPEC `(ks:num->real^N->bool) i` RDT_INTK_ONE_POS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN RDT_NN_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `inv(K pow 3)` THEN EXISTS_TAC `C1 * (&1 + MJ)` THEN
  EXISTS_TAC `sum {i | i < n0}
                (\i. &2 * C2 pow 2 *
                     (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
                      &(CARD(pde_index_lists s (:N))) * (DD:num->real) i * K))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `g:A->real^N^N`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pde_tensor_smooth atlas (g:A->real^N^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i y. i < n0 /\ y IN ks i
          ==> metric_field (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                           (metric_local atlas (cs i) (g:A->real^N^N)) /\
              metric_field (IMAGE (SND(cs i)) (FST(cs i)))
                           (metric_local atlas (cs i) (h:A->real^N^N)) /\
              y IN IMAGE (SND(cs i)) (FST(cs i)) /\
              norm((vectorize:real^N^N->real^(N,N)finite_prod) (metric_local atlas (cs i) g y))
              <= K /\
              (!w. norm w pow 2 <= K * (w dot (metric_local atlas (cs i) g y ** w))) /\
              pde_jetn (s - dimindex(:N))
                ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) g) y
              <= MJ /\
              pde_jetn m
                ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) h) y
              <= BH /\
              norm((vectorize:real^N^N->real^(N,N)finite_prod)
                     (matrix_inv(metric_local atlas (cs i) h y))) <= LH`
  (LABEL_TAC "pt") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `0`; `K:real`;
                   `g:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `m:num`; `B:real`;
                   `h:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                   (metric_local atlas (cs i) (g:A->real^N^N)) /\
      metric_field (IMAGE (SND(cs i)) (FST(cs i))) (metric_local atlas (cs i) (h:A->real^N^N))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    SUBGOAL_THEN `y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `pde_jetn (s - dimindex(:N))
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y
                  <= MJ` ASSUME_TAC
    THENL
     [USE_THEN "sob" (MP_TAC o SPECL [`g:A->real^N^N`; `K:real`; `i:num`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                    (matrix_inv(metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                 (h:A->real^N^N) y))) <= LH` ASSUME_TAC
    THENL [EXPAND_TAC "LH" THEN MATCH_MP_TAC RDT_INV_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`; `w:real^N`] THEN STRIP_TAC THEN
    USE_THEN "pt" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MP_TAC(ISPECL [`K:real`; `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                (g:A->real^N^N) y`] RDT_INV_LOWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "pt" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C1 * (&1 + pde_jetn (s DIV 2 + 1)
                         ((vectorize:real^N^N->real^(N,N)finite_prod) o
                          metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                       (g:A->real^N^N)) y)` THEN
    CONJ_TAC THENL
     [USE_THEN "c1" MATCH_MP_TAC THEN
      EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `pde_jetn (s - dimindex(:N))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y`;
        EXISTS_TAC `pde_jetn m
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)) y`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `pde_jetn (s - dimindex(:N))
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`\i. &2 * C2 pow 2 *
                      (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
                       &(CARD(pde_index_lists s (:N))) * (DD:num->real) i * K)`;
                 `n0:num`; `i:num`] RDT_TERM_LE_SUM) THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= z ==> x <= z`) THEN
  SUBGOAL_THEN
   `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) /\
    metric_field U (metric_local atlas (cs i) (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(TH:num->A->real) i`;
                 `(KT:num->real^N->bool) i`; `g:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   (g:A->real^N^N))` THEN
    SIMP_TAC[metric_field];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                     (g:A->real^N^N)`;
                 `metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)`]
    RDT_COEF_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * C2 pow 2 *
              (drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1))) +
               &(CARD(pde_index_lists s (:N))) *
               rdt_hs U s (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                 ((TH:num->A->real) i
                                    (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                                  metric_local atlas (cs i) (g:A->real^N^N) z)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RDT_INTK_TOPJET THEN EXISTS_TAC `(KT:num->real^N->bool) i` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RDT_CJET_CONT THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o SPECL [`i:num`; `y:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
      REWRITE_TAC[RDT_CJET_POS] THEN
      SUBGOAL_THEN
       `pde_jetn s (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                          ((TH:num->A->real) i
                             (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                           metric_local atlas (cs i) (g:A->real^N^N) z)) y =
        pde_jetn s ((vectorize:real^N^N->real^(N,N)finite_prod) o
                    metric_local atlas (cs i) g) y`
      SUBST1_TAC THENL
       [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `(OO:num->real^N->bool) i` THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[o_THM; MATRIX_CMUL_LID];
        ALL_TAC] THEN
      USE_THEN "c2" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `pde_jetn (s - dimindex(:N))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y`;
        EXISTS_TAC `pde_jetn m
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o
                       metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)) y`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LADD_IMP THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(DD:num->real) i * pde_mnorm2 atlas n0 cs psi s (g:A->real^N^N)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool`))
          (concl th) && is_forall (concl th) &&
      can (find_term ((=) `rdt_hs:(real^N->bool)->num->(real^N->real^(N,N)finite_prod)->real`))
          (concl th))) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The pointwise facts on the pieces for metrics of the ball,                *)
(* and the H^(s-1) bound of the remainder P_h(g) - tr_g Hess_h g (the        *)
(* forcing of the step) for g in the ball.                                   *)
(* ------------------------------------------------------------------------- *)

let RDT_BALL_PT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     dimindex(:N) <= s /\ &0 <= B /\ &0 <= K
     ==> ?MJ. &0 <= MJ /\
              !h g i y.
                riemannian_metric atlas h /\ pde_cbound atlas n0 cs ks m B h /\
                riemannian_metric atlas g /\ pde_cbound atlas n0 cs ks 0 K g /\
                pde_mnorm2 atlas n0 cs psi s g <= K /\ i < n0 /\ y IN ks i
                ==> metric_field (IMAGE (SND(cs i)) (FST(cs i))) (metric_local atlas (cs i) g) /\
                    metric_field (IMAGE (SND(cs i)) (FST(cs i))) (metric_local atlas (cs i) h) /\
                    y IN IMAGE (SND(cs i)) (FST(cs i)) /\
                    norm((vectorize:real^N^N->real^(N,N)finite_prod)
                           (metric_local atlas (cs i) g y)) <= K /\
                    (!w. norm w pow 2 <= K * (w dot (metric_local atlas (cs i) g y ** w))) /\
                    pde_jetn (s - dimindex(:N))
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) g) y
                    <= MJ /\
                    pde_jetn m
                      ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) h) y
                    <= &(CARD(pde_index_lists m (:N))) * B /\
                    norm((vectorize:real^N^N->real^(N,N)finite_prod)
                           (matrix_inv(metric_local atlas (cs i) h y)))
                    <= &(dimindex(:N) * dimindex(:N)) * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s - dimindex(:N)`] RDT_SOB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s - dimindex(:N) + dimindex(:N) = s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `CJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sob"))) THEN
  EXISTS_TAC `CJ * (&1 + K)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `0`; `K:real`;
                   `g:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                   `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `m:num`; `B:real`;
                   `h:A->real^N^N`; `i:num`; `y:real^N`] RDT_CBOUND_PT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `metric_field (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                   (metric_local atlas (cs i) (g:A->real^N^N)) /\
      metric_field (IMAGE (SND(cs i)) (FST(cs i))) (metric_local atlas (cs i) (h:A->real^N^N))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
    SUBGOAL_THEN `y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `pde_tensor_smooth atlas (g:A->real^N^N)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH]; ALL_TAC] THEN
    SUBGOAL_THEN `pde_jetn (s - dimindex(:N))
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y
                  <= CJ * (&1 + K)` ASSUME_TAC
    THENL
     [USE_THEN "sob" (MP_TAC o SPECL [`g:A->real^N^N`; `K:real`; `i:num`; `y:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((vectorize:real^N^N->real^(N,N)finite_prod)
                    (matrix_inv(metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                 (h:A->real^N^N) y))) <= &(dimindex(:N) * dimindex(:N)) * B`
    ASSUME_TAC THENL [MATCH_MP_TAC RDT_INV_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

let RDT_KF_SMOOTH = prove
 (`!U (G:real^N->real^N^N) H.
     metric_field U G /\ metric_field U H ==> smooth_map_on U (rdt_kf G H)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(U:real^N->bool) /\
                smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o G)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on U (rdt_dgv (G:real^N->real^N^N))` ASSUME_TAC THENL
   [REWRITE_TAC[RDT_DGV_FUN] THEN MATCH_MP_TAC RDT_SMOOTH_VLAMBDA THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[RDT_KF_FUN] THEN MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `smooth_map_on U ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                  (G:real^N->real^N^N))` THEN
    REWRITE_TAC[o_DEF];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN REWRITE_TAC[ETA_AX] THEN
    ASM_SIMP_TAC[RDT_GV_SMOOTH; RDT_GDV_SMOOTH]]);;

(* The chart representative of the remainder is rdt_psi o rdt_kf.          *)

let RDT_FORCING_CHART = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N) (g:A->real^N^N).
     smooth_manifold_atlas top atlas /\ c IN atlas /\
     riemannian_metric atlas h /\ riemannian_metric atlas g
     ==> (!z. z IN IMAGE (SND c) (FST c)
              ==> (vectorize:real^N^N->real^(N,N)finite_prod)
                    (metric_local atlas c
                       (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) z) =
                  rdt_psi (rdt_kf (metric_local atlas c g) (metric_local atlas c h) z)) /\
         smooth_map_on (IMAGE (SND c) (FST c))
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                  (metric_local atlas c
                     (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)) (metric_local atlas c g) /\
    metric_field (IMAGE (SND c) (FST c)) (metric_local atlas c (h:A->real^N^N)) /\
    open(IMAGE (SND c) (FST c))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[riemannian_metric]; ASM_MESON_TAC[riemannian_metric];
      ASM_MESON_TAC[PDM_CHART_OPEN_C]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
        ==> (vectorize:real^N^N->real^(N,N)finite_prod)
              (metric_local atlas c
                 (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) z) =
            rdt_psi (rdt_kf (metric_local atlas c (g:A->real^N^N))
                            (metric_local atlas c (h:A->real^N^N)) z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `c:(A->bool)#(A->real^N)`; `h:A->real^N^N`; `g:A->real^N^N`;
                   `pde_rdt_sym (metric_local atlas (c:(A->bool)#(A->real^N)) (h:A->real^N^N))`;
                   `z:real^N`] RDT_REM_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RDT_SYM_ID THEN
      EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RDT_PSI_KF THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `rdt_psi o rdt_kf (metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N))
                               (metric_local atlas c (h:A->real^N^N))` THEN
  ASM_SIMP_TAC[o_THM] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{x:real^((N,N)finite_prod,((N,(N,N)finite_prod)finite_prod,
                 ((N,(N,N)finite_prod)finite_prod,
                  (N,(N,(N,N)finite_prod)finite_prod)finite_prod)finite_sum)finite_sum)finite_sum |
               ~(det((matrify:real^(N,N)finite_prod->real^N^N) (fstcart x)) = &0)}` THEN
  ASM_SIMP_TAC[RDT_KF_SMOOTH; RDT_PSI_SMOOTH] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RDT_OPEN_INV THEN REWRITE_TAC[LINEAR_FSTCART]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; rdt_kf; FSTCART_PASTECART;
              MATRIFY_VECTORIZE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) (g:A->real^N^N)`;
                 `SND (c:(A->bool)#(A->real^N)) x`] LRG_METRIC_INVERTIBLE) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* |P_h(g) - tr_g Hess_h g|_(s-1)^2 <= CF for g in the ball                  *)
(* (RDT_HS_FROM_POINTWISE per chart: the cut-off forcing psi_i F_i has jets  *)
(* bounded by the top jet of theta_i g_i, RDT_REM_JETN).                     *)
(* ------------------------------------------------------------------------- *)

let RDT_BALL_FORCING = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi s m B K.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ compact_space top /\
     pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
     (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
     2 * dimindex(:N) + 4 <= s /\ s + 3 <= m /\ &0 <= B /\ &0 <= K
     ==> ?CF. &0 <= CF /\
           !h g. riemannian_metric atlas h /\ pde_cbound atlas n0 cs ks m B h /\
                 riemannian_metric atlas g /\ pde_cbound atlas n0 cs ks 0 K g /\
                 pde_mnorm2 atlas n0 cs psi s g <= K
                 ==> pde_mnorm2 atlas n0 cs psi (s - 1)
                       (\x. pde_rdt_rhs atlas h g x - pde_trhess atlas g h g x) <= CF`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`]
    RDT_COVER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `s - 1`] RDT_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `TH:num->A->real` (X_CHOOSE_THEN `KT:num->real^N->bool`
    (X_CHOOSE_THEN `OO:num->real^N->bool` (X_CHOOSE_THEN `DD:num->real`
    (X_CHOOSE_THEN `AP:num->real` (LABEL_TAC "cd")))))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `n0:num`;
                 `cs:num->(A->bool)#(A->real^N)`; `ks:num->real^N->bool`; `psi:num->A->real`;
                 `s:num`; `m:num`; `B:real`; `K:real`] RDT_BALL_PT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `MJ:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))) THEN
  SUBGOAL_THEN `(s - 1) DIV 2 + 2 <= s - dimindex(:N) /\ (s - 1) + 3 <= m /\ (s - 1) + 1 = s`
  STRIP_ASSUME_TAC THENL [MP_TAC(SPEC `s - 1` RDT_DIV2) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s - 1`; `K:real`; `MJ:real`; `&(CARD(pde_index_lists m (:N))) * B`;
                `&(dimindex(:N) * dimindex(:N)) * B`] RDT_REM_JETN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `CR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cr"))) THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> &0 <= (AP:num->real) i /\ &0 <= (DD:num->real) i /\
                   &0 <= drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_ONE] THEN MATCH_MP_TAC RDT_INTK_ONE_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `APS = sum {i | i < n0} (AP:num->real)` THEN
  ABBREV_TAC `DS = sum {i | i < n0} (DD:num->real)` THEN
  ABBREV_TAC `IS = sum {i | i < n0}
                     (\i. drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))))` THEN
  SUBGOAL_THEN
   `!i. i < n0 ==> (AP:num->real) i <= APS /\ (DD:num->real) i <= DS /\
                   drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2))) <= IS`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["APS"; "DS"; "IS"] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`AP:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM);
      MP_TAC(ISPECL [`DD:num->real`; `n0:num`; `i:num`] RDT_TERM_LE_SUM);
      MP_TAC(ISPECL [`\i. drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))`;
                     `n0:num`; `i:num`] RDT_TERM_LE_SUM)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= APS /\ &0 <= DS /\ &0 <= IS` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["APS"; "DS"; "IS"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    ALL_TAC] THEN
  ABBREV_TAC `c1 = &(CARD(pde_index_lists (s - 1) (:N))) *
                   (&2 pow (s - 1) * &1 * &s * APS) * CR` THEN
  SUBGOAL_THEN `&0 <= c1` ASSUME_TAC THENL [EXPAND_TAC "c1" THEN RDT_NN_TAC; ALL_TAC] THEN
  ABBREV_TAC `FC = &(CARD(pde_index_lists (s - 1) (:N))) *
                   (&2 * c1 pow 2 * (&1 pow 2 * &(CARD(pde_index_lists s (:N))) * (DS * K) +
                                     &1 pow 2 * IS))` THEN
  SUBGOAL_THEN `&0 <= FC` ASSUME_TAC THENL [EXPAND_TAC "FC" THEN RDT_NN_TAC; ALL_TAC] THEN
  EXISTS_TAC `&n0 * FC` THEN CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
                                         ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`h:A->real^N^N`; `g:A->real^N^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[pde_mnorm2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {i | i < n0} (\i:num. FC)` THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_LE_REFL]] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ABBREV_TAC `U = IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
  ABBREV_TAC `Fg = \x. pde_rdt_rhs atlas (h:A->real^N^N) g x - pde_trhess atlas g h g x` THEN
  USE_THEN "cf" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  USE_THEN "cd" (MP_TAC o SPEC `i:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `h:A->real^N^N`; `g:A->real^N^N`]
    RDT_FORCING_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`] RDT_CUTOFF_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) /\
    metric_field U (metric_local atlas (cs i) (h:A->real^N^N))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "U" THEN ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(TH:num->A->real) i`;
                 `(KT:num->real^N->bool) i`; `g:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `metric_field U (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                   (g:A->real^N^N))` THEN
    SIMP_TAC[metric_field];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                 `(ks:num->real^N->bool) i`; `Fg:A->real^N^N`] RDT_PIECE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[o_DEF]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `rdt_hs U (s - 1)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
              metric_local atlas (cs i) (Fg:A->real^N^N) z)) <= FC`
  MP_TAC THENL [ALL_TAC; REWRITE_TAC[rdt_hs; rdt_int]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&(CARD(pde_index_lists (s - 1) (:N))) *
    (&2 * c1 pow 2 *
     (&1 pow 2 * &(CARD(pde_index_lists s (:N))) *
      rdt_hs U s (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                         metric_local atlas (cs i) (g:A->real^N^N) z)) +
      &1 pow 2 * drop(integral ((ks:num->real^N->bool) i) (\y. lift(&1 pow 2)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "FC" THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(DD:num->real) i * pde_mnorm2 atlas n0 cs psi s (g:A->real^N^N)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `pde_tensor_smooth:(((A->bool)#(A->real^N))->bool)->(A->real^N^N)->bool`))
              (concl th) && is_forall (concl th) &&
          can (find_term ((=) `rdt_hs:(real^N->bool)->num->(real^N->real^(N,N)finite_prod)->real`))
              (concl th))) THEN
        ASM_SIMP_TAC[PDM_TENSOR_SMOOTH_EQ; RIEMANNIAN_METRIC_TENSOR2_SMOOTH];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(DD:num->real) i * K` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[]];
      ASM_SIMP_TAC[]]] THEN
  MATCH_MP_TAC RDT_HS_FROM_POINTWISE THEN
  MAP_EVERY EXISTS_TAC [`(ks:num->real^N->bool) i`; `(KT:num->real^N->bool) i`;
                        `\y:real^N. &1`] THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_CONST; REAL_LE_REFL; REAL_POS] THEN
  MAP_EVERY X_GEN_TAC [`l:num list`; `y:real^N`] THEN STRIP_TAC THEN
  USE_THEN "pt" (MP_TAC o SPECL [`h:A->real^N^N`; `g:A->real^N^N`; `i:num`; `y:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `pde_jetn (s - 1)
                (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                        metric_local atlas (cs i) (Fg:A->real^N^N) z)) y` THEN
  CONJ_TAC THENL [MATCH_MP_TAC PDE_ME_TERM_LE_JETN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\(x:real^1) (v:real^(N,N)finite_prod). drop x % v`; `&1`; `s - 1`;
                 `U:real^N->bool`;
                 `\z. lift((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z))`;
                 `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                        (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (Fg:A->real^N^N) z)`;
                 `y:real^N`; `(AP:num->real) i`] RDT_JETN_BILINEAR_BOUNDED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INST_TYPE [`:N`,`:Q`] RDT_BB_E2; REAL_POS]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; GSYM VECTORIZE_CMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN
   `pde_jetn (s - 1)
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (Fg:A->real^N^N) z)) y =
    pde_jetn (s - 1)
      (\z. rdt_psi (rdt_kf (metric_local atlas (cs i) (g:A->real^N^N))
                           (metric_local atlas (cs i) (h:A->real^N^N)) z)) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn s (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                      ((TH:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) z) %%
                       metric_local atlas (cs i) (g:A->real^N^N) z)) y =
    pde_jetn s ((vectorize:real^N^N->real^(N,N)finite_prod) o metric_local atlas (cs i) g) y`
  SUBST1_TAC THENL
   [MATCH_MP_TAC P2CT_JETN_LOCAL THEN EXISTS_TAC `(OO:num->real^N->bool) i` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[o_THM; MATRIX_CMUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pde_jetn (s - 1)
      (\z. rdt_psi (rdt_kf (metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                         (g:A->real^N^N))
                           (metric_local atlas (cs i) (h:A->real^N^N)) z)) y <=
    CR * (&1 + pde_jetn s ((vectorize:real^N^N->real^(N,N)finite_prod) o
                           metric_local atlas (cs i) g) y)`
  ASSUME_TAC THENL
   [USE_THEN "cr" MATCH_MP_TAC THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `pde_jetn (s - dimindex(:N))
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (g:A->real^N^N)) y`;
      EXISTS_TAC `pde_jetn m
                    ((vectorize:real^N^N->real^(N,N)finite_prod) o
                     metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i) (h:A->real^N^N)) y`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PDE_JETN_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = pde_jetn s ((vectorize:real^N^N->real^(N,N)finite_prod) o
                              metric_local atlas ((cs:num->(A->bool)#(A->real^N)) i)
                                           (g:A->real^N^N)) y` THEN
  SUBGOAL_THEN `&0 <= J /\ &0 <= CR /\ (AP:num->real) i <= APS /\ &0 <= AP i` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "J" THEN ASM_SIMP_TAC[PDE_JETN_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "c1" THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(pde_index_lists (s - 1) (:N))) * (&2 pow (s - 1) * &1 * &s * (AP:num->real) i) *
              (CR * (&1 + J))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN RDT_NN_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 * J + &1 * &1 = &1 + J`; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC);;

