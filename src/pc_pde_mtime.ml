(* ========================================================================= *)
(* Unit pc_pde_mtime (PDE layer, time regularity of the chart-wise norms):   *)
(* the chart norms pde_mnorm2 s (v t) of a pde_tfam_from family v are        *)
(* continuous in t up to time a and differentiable for a < t < b, with the   *)
(* derivative given by the chart pieces and their time partials (the chart   *)
(* analogue of PDE_HS2_SLICE_DERIV of pc_pde_tlin).                          *)
(* ========================================================================= *)

needs "src/pc_pde_mloc.ml";;
needs "src/pc_pde_tlin.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The time derivative of the squared jet integrals over a box of            *)
(* a space-time family (the per-list core of PDE_HS2_SLICE_DERIV of          *)
(* pc_pde_tlin, over an arbitrary box; the proof is that of                  *)
(* PDE_HS2_SLICE_DERIV with interval[vec 0,vec 1] replaced).                 *)
(* ========================================================================= *)

let PDM_BOX_SQJET_DERIV = prove
 (`!(FU:real^(1,N)finite_sum->real^K) a b (c:real^N) d l t.
     smooth_map_on (interval(lift a,lift b) PCROSS (:real^N)) FU /\ a < t /\ t < b /\
     ALL (\i. 1 <= i /\ i <= dimindex(:N)) l
     ==> ((\r. drop(integral (interval[c,d])
                 (\y. lift(norm(iterated_partial l (\y. FU(pastecart (lift r) y)) y) pow 2))))
          has_real_derivative
          drop(integral (interval[c,d])
                 (\y. lift(&2 * (iterated_partial l (\y. FU(pastecart (lift t) y)) y dot
                                 iterated_partial l
                                   (\y. partial_derivative 1 FU (pastecart (lift t) y)) y)))))
         (atreal t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = interval(lift a,lift b) PCROSS (:real^N)` THEN
  SUBGOAL_THEN `open (S:real^(1,N)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!w (y:real^N). w IN interval(lift a,lift b) ==> pastecart w y IN S`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[PASTECART_IN_PCROSS; IN_UNIV]; ALL_TAC] THEN
  ABBREV_TAC `L = MAP (\k. 1 + k) (l:num list)` THEN
  SUBGOAL_THEN `ALL (\i. 1 <= i /\ i <= dimindex(:(1,N)finite_sum)) (L:num list)`
  ASSUME_TAC THENL [EXPAND_TAC "L" THEN ASM_SIMP_TAC[PDE_MAP_SUC_RANGE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (iterated_partial L (FU:real^(1,N)finite_sum->real^K)) /\
    smooth_map_on S (partial_derivative 1 (FU:real^(1,N)finite_sum->real^K))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MAP_ON_ITERATED_PARTIAL; SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  ABBREV_TAC `G = \z. lift(norm(iterated_partial L (FU:real^(1,N)finite_sum->real^K) z) pow 2)` THEN
  SUBGOAL_THEN `smooth_map_on S (G:real^(1,N)finite_sum->real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC SMOOTH_MAP_ON_NORM_POW2_OPEN THEN
    ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval(lift a,lift b)`; `S:real^(1,N)finite_sum->bool`;
                 `c:real^N`; `d:real^N`; `G:real^(1,N)finite_sum->real^1`]
                NS_PARAM_INTEGRAL_SMOOTH) THEN
  ASM_SIMP_TAC[OPEN_INTERVAL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lift t IN interval(lift a,lift b)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\w. integral (interval[c,d])
            (\x. (G:real^(1,N)finite_sum->real^1)(pastecart w x))) has_vector_derivative
     partial_derivative 1 (\w. integral (interval[c,d]) (\x. G(pastecart w x)))
       (lift t)) (at (lift t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_HEAT_VDERIV1 THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `interval(lift a,lift b)` THEN ASM_REWRITE_TAC[OPEN_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. partial_derivative 1 (G:real^(1,N)finite_sum->real^1) (pastecart (lift t) x) =
               lift(&2 * (iterated_partial L (FU:real^(1,N)finite_sum->real^K)
                            (pastecart (lift t) x) dot
                          partial_derivative 1 (iterated_partial L FU) (pastecart (lift t) x)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "G" THEN REWRITE_TAC[NORM_POW_2] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) PDE_PARTIAL_DOT o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[ETA_AX];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM LIFT_ADD; LIFT_EQ; ETA_AX] THEN
    MP_TAC(ISPECL [`partial_derivative 1 (iterated_partial L (FU:real^(1,N)finite_sum->real^K))
                      (pastecart (lift t) x)`;
                   `iterated_partial L (FU:real^(1,N)finite_sum->real^K) (pastecart (lift t) x)`]
                  DOT_SYM) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC `\r. drop(integral (interval[c,d])
                        (\x. (G:real^(1,N)finite_sum->real^1)(pastecart (lift r) x)))` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_SUB_LT] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN EXPAND_TAC "L" THEN
    MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`abs(r - t) < min (t - a) (b - t)`; `a < t`; `t < b`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_VECTOR_DERIVATIVE_AT] THEN
  SUBGOAL_THEN
   `lift o (\r. drop(integral (interval[c,d])
                       (\x. (G:real^(1,N)finite_sum->real^1)(pastecart (lift r) x)))) o drop =
    (\w. integral (interval[c,d]) (\x. G(pastecart w x)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `partial_derivative 1
      (\w. integral (interval[c,d])
             (\x. (G:real^(1,N)finite_sum->real^1)(pastecart w x))) (lift t) =
    lift(drop(integral (interval[c,d])
           (\y. lift(&2 * (iterated_partial l
                              (\y. (FU:real^(1,N)finite_sum->real^K)(pastecart (lift t) y)) y dot
                            iterated_partial l
                              (\y. partial_derivative 1 FU (pastecart (lift t) y)) y)))))`
  (SUBST1_TAC o SYM) THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[LIFT_DROP] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:real^(1,N)finite_sum->real^1`; `lift t`; `x:real^N`]
                PDE_HEAT_TIME_SLICE_PARTIAL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `S:real^(1,N)finite_sum->bool` THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
   [CONV_TAC SYM_CONV THEN EXPAND_TAC "L" THEN MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^(1,N)finite_sum->bool`; `FU:real^(1,N)finite_sum->real^K`; `1`]
                TEXT_PARTIAL_COMMUTE_ITERATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[PDE_HEAT_DIMINDEX_ST] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `L:num list`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `pastecart (lift t) (x:real^N)`) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN EXPAND_TAC "L" THEN
  MATCH_MP_TAC PDE_SLAB_SLICE_ITERATED THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The chart norms of pde_tfam_from families as box integrals of             *)
(* zero-extended chart pieces; continuity and derivative in time.            *)
(* ========================================================================= *)

(* Integrals over two sets agree for maps vanishing off a common subset.    *)

let PDM_INTEGRAL_SUPPORT_EQ = prove
 (`!(f:real^M->real^N) s t k.
        k SUBSET s /\ k SUBSET t /\ (!y. ~(y IN k) ==> f y = vec 0)
        ==> integral s f = integral t f`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real^M` THEN
  ASM_CASES_TAC `(y:real^M) IN k` THENL [ASM SET_TAC[]; ASM_SIMP_TAC[COND_ID]]);;

(* The cut-off chart pieces of a pde_tfam_from family, extended by zero,    *)
(* are smooth up to time a on the whole space.                               *)

let PDM_TFAM_PIECE_UPTO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (c:(A->bool)#(A->real^N))
    (psi:A->real) k (v:real->A->real^N^N) a b.
        smooth_manifold_atlas top atlas /\ c IN atlas /\
        mfd_smooth atlas (\x. lift(psi x)) /\ compact k /\ k SUBSET IMAGE (SND c) (FST c) /\
        (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) k) /\
        pde_tfam_from atlas a b v
        ==> pde_upto a b (:real^N)
              (\t y. if y IN IMAGE (SND c) (FST c)
                     then (vectorize:real^N^N->real^(N,N)finite_prod)
                            (psi(chart_inv c y) %% metric_local atlas c (v t) y)
                     else vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_OPEN_C) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c) /\ ~(y IN k)
        ==> (psi:A->real) (chart_inv c y) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN IMAGE (chart_inv c) k` MP_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x:A. ~((psi:A->real) x = &0)
                              ==> x IN IMAGE (chart_inv (c:(A->bool)#(A->real^N))) k`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) = z` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) (chart_inv c y)` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)`;
                 `\t y. (vectorize:real^N^N->real^(N,N)finite_prod)
                          (metric_local atlas (c:(A->bool)#(A->real^N)) ((v:real->A->real^N^N) t) y)`;
                 `\y. if y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
                      then (psi:A->real) (chart_inv c y) else &0`;
                 `k:real^N->bool`] PDM_UPTO_CUTOFF_EXT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `pde_tfam_from atlas a b (v:real->A->real^N^N)` THEN
      REWRITE_TAC[PDM_TFAM_FROM_UPTO] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN
       `(\y. lift(if y IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)
                  then (psi:A->real) (chart_inv c y) else &0)) =
        (\y. if y IN IMAGE (SND c) (FST c) then ((\x. lift(psi x)) o chart_inv c) y
             else vec 0)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[LIFT_NUM];
        ALL_TAC] THEN
      MATCH_MP_TAC PDM_ZERO_EXT_SMOOTH THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [UNDISCH_TAC `mfd_smooth (atlas:((A->bool)#(A->real^N))->bool) (\x. lift((psi:A->real) x))` THEN
        REWRITE_TAC[mfd_smooth] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM; LIFT_NUM]];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] PDM_UPTO_CONG) th)) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTORIZE_CMUL]);;

(* A cutoff supported in the image of k vanishes off k in the chart.       *)

let PDM_CUTOFF_CHART_ZERO = prove
 (`!top atlas (c:(A->bool)#(A->real^N)) (psi:A->real) k y.
        smooth_manifold_atlas top atlas /\ c IN atlas /\ k SUBSET IMAGE (SND c) (FST c) /\
        (!x. ~(psi x = &0) ==> x IN IMAGE (chart_inv c) k) /\
        y IN IMAGE (SND c) (FST c) /\ ~(y IN k)
        ==> psi(chart_inv c y) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `c:(A->bool)#(A->real^N)`] PDM_CHART_INV_C) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^N)) y IN IMAGE (chart_inv c) k` MP_TAC THENL
   [MATCH_MP_TAC(ASSUME `!x:A. ~((psi:A->real) x = &0)
                            ==> x IN IMAGE (chart_inv (c:(A->bool)#(A->real^N))) k`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^N) IN IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) = z` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SND(c:(A->bool)#(A->real^N)) (chart_inv c y)` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

(* Time regularity of the chart norms: t -> pde_mnorm2 s (v t) for a        *)
(* pde_tfam_from family v is continuous on [a,t1] for t1 < b and            *)
(* differentiable for a < t < b.                                            *)

let PDM_MNORM2_TFAM_DERIV = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) n0 cs ks psi
    (v:real->A->real^N^N) a b s.
        smooth_manifold_atlas top atlas /\
        pde_cover (top,atlas) n0 cs ks /\ pde_cutoffs (top,atlas) n0 cs psi /\
        (!i x. i < n0 /\ ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i)) /\
        pde_tfam_from atlas a b v
        ==> (!t1. t1 < b
                  ==> (\r. pde_mnorm2 atlas n0 cs psi s (v r))
                      real_continuous_on real_interval[a,t1]) /\
            (!t. a < t /\ t < b
                 ==> ((\r. pde_mnorm2 atlas n0 cs psi s (v r)) has_real_derivative
                      sum {i | i < n0}
                        (\i. sum (pde_index_lists s (:N))
                          (\l. drop(integral (IMAGE (SND(cs i)) (FST(cs i)))
                                 (\z. lift(&2 *
                                   (iterated_partial l
                                      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                             (psi i (chart_inv (cs i) z) %%
                                              metric_local atlas (cs i) (v t) z)) z dot
                                    iterated_partial l
                                      (\z. partial_derivative 1
                                             (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                                    (psi i (chart_inv (cs i) (sndcart w)) %%
                                                     metric_local atlas (cs i)
                                                       (v (drop(fstcart w))) (sndcart w)))
                                             (pastecart (lift t) z)) z)))))))
                     (atreal t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* chart facts *)
  SUBGOAL_THEN
   `!i. i < n0
        ==> (cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
            ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
            mfd_smooth atlas (\x. lift((psi:num->A->real) i x)) /\
            open(IMAGE (SND(cs i)) (FST(cs i))) /\
            (!x. ~(psi i x = &0) ==> x IN IMAGE (chart_inv (cs i)) (ks i))`
  (LABEL_TAC "cf") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(cs:num->(A->bool)#(A->real^N)) i IN atlas /\ compact((ks:num->real^N->bool) i) /\
      ks i SUBSET IMAGE (SND(cs i)) (FST(cs i)) /\
      mfd_smooth atlas (\x. lift((psi:num->A->real) i x))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `pde_cover (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) ks` THEN
      UNDISCH_TAC `pde_cutoffs (top,atlas) n0 (cs:num->(A->bool)#(A->real^N)) psi` THEN
      REWRITE_TAC[pde_cover; pde_cutoffs] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `(cs:num->(A->bool)#(A->real^N)) i`] PDM_CHART_OPEN_C) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ASSUME `!i x. i < n0 /\ ~((psi:num->A->real) i x = &0)
                              ==> x IN IMAGE (chart_inv ((cs:num->(A->bool)#(A->real^N)) i))
                                             ((ks:num->real^N->bool) i)`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* space-time extensions of the zero-extended pieces, and boxes *)
  SUBGOAL_THEN
   `?EE (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) cc dd.
      !i. i < n0
          ==> &0 < EE i /\
              smooth_map_on (interval(lift(a - EE i),lift b) PCROSS (:real^N)) (FU i) /\
              (!t y. a <= t /\ t < b
                     ==> FU i (pastecart (lift t) y) =
                         if y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))
                         then (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((psi:num->A->real) i (chart_inv (cs i) y) %%
                                 metric_local atlas (cs i) ((v:real->A->real^N^N) t) y)
                         else vec 0) /\
              (ks:num->real^N->bool) i SUBSET interval[cc i:real^N,dd i]`
  (X_CHOOSE_THEN `EE:num->real` (X_CHOOSE_THEN
     `FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod` (X_CHOOSE_THEN `cc:num->real^N`
     (X_CHOOSE_THEN `dd:num->real^N` (LABEL_TAC "ext"))))) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                   `(ks:num->real^N->bool) i`; `v:real->A->real^N^N`; `a:real`; `b:real`]
                  PDM_TFAM_PIECE_UPTO) THEN
    ASM_REWRITE_TAC[pde_upto; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
      `F1:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPEC `(ks:num->real^N->bool) i` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real^N` (X_CHOOSE_TAC `d0:real^N`)) THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `F1:real^(1,N)finite_sum->real^(N,N)finite_prod`;
                          `c0:real^N`; `d0:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the extensions vanish off the pieces *)
  SUBGOAL_THEN
   `!i r y. i < n0 /\ a <= r /\ r < b /\ ~(y IN (ks:num->real^N->bool) i)
            ==> (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                  (pastecart (lift r) y) = vec 0`
  (LABEL_TAC "fz") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    USE_THEN "ext" (fun th -> MP_TAC(SPECL [`r:real`; `y:real^N`]
      (CONJUNCT1(CONJUNCT2(CONJUNCT2(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(cs:num->(A->bool)#(A->real^N)) i`; `(psi:num->A->real) i`;
                   `(ks:num->real^N->bool) i`; `y:real^N`] PDM_CUTOFF_CHART_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MATRIX_CMUL_LZERO; VECTORIZE_0];
    ALL_TAC] THEN
  (* on the chart images the extensions are the pieces *)
  SUBGOAL_THEN
   `!i r y. i < n0 /\ a <= r /\ r < b /\
            y IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))
            ==> (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                  (pastecart (lift r) y) =
                (vectorize:real^N^N->real^(N,N)finite_prod)
                  ((psi:num->A->real) i (chart_inv (cs i) y) %%
                   metric_local atlas (cs i) ((v:real->A->real^N^N) r) y)`
  (LABEL_TAC "fp") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "ext" (fun th -> MP_TAC(SPECL [`r:real`; `y:real^N`]
      (CONJUNCT1(CONJUNCT2(CONJUNCT2(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the norm terms as box integrals *)
  SUBGOAL_THEN
   `!i l r. i < n0 /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l /\ a <= r /\ r < b
            ==> drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                  (\y. lift(norm(iterated_partial l
                         (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                                ((psi:num->A->real) i (chart_inv (cs i) z) %%
                                 metric_local atlas (cs i) ((v:real->A->real^N^N) r) z)) y)
                         pow 2))) =
                drop(integral (interval[(cc:num->real^N) i,dd i])
                  (\y. lift(norm(iterated_partial l
                         (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                                (pastecart (lift r) y)) y) pow 2)))`
  (LABEL_TAC "box1") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    USE_THEN "ext" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
        (\y. lift(norm(iterated_partial l
               (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                      (pastecart (lift r) y)) y) pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
      EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "fp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PDM_INTEGRAL_SUPPORT_EQ THEN EXISTS_TAC `(ks:num->real^N->bool) i` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `iterated_partial l
          (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i (pastecart (lift r) y))
          y = vec 0`
      (fun th -> REWRITE_TAC[th; NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
                 REWRITE_TAC[LIFT_NUM]) THEN
      MATCH_MP_TAC PDM_PARTIAL_ZERO_OFF THEN
      MAP_EVERY EXISTS_TAC [`(:real^N)`; `(ks:num->real^N->bool) i`] THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      USE_THEN "fz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. a <= r /\ r < b
        ==> pde_mnorm2 atlas n0 cs psi s ((v:real->A->real^N^N) r) =
            sum {i | i < n0}
              (\i. sum (pde_index_lists s (:N))
                 (\l. drop(integral (interval[(cc:num->real^N) i,dd i])
                        (\y. lift(norm(iterated_partial l
                               (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                                      (pastecart (lift r) y)) y) pow 2)))))`
  (LABEL_TAC "box") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[pde_mnorm2] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:num list` THEN
    REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "box1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* each box term is differentiable in time below b and above a - EE i *)
  SUBGOAL_THEN
   `!i l r. i < n0 /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l /\
            a - (EE:num->real) i < r /\ r < b
            ==> ((\r. drop(integral (interval[(cc:num->real^N) i,dd i])
                         (\y. lift(norm(iterated_partial l
                                (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                                       (pastecart (lift r) y)) y) pow 2))))
                 has_real_derivative
                 drop(integral (interval[cc i,dd i])
                   (\y. lift(&2 * (iterated_partial l (\y. FU i (pastecart (lift r) y)) y dot
                                   iterated_partial l
                                     (\y. partial_derivative 1 (FU i) (pastecart (lift r) y))
                                     y))))) (atreal r)`
  (LABEL_TAC "bd") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PDM_BOX_SQJET_DERIV THEN
    EXISTS_TAC `a - (EE:num->real) i` THEN EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ext" (fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2(MP (SPEC `i:num` th)
      (ASSUME `(i:num) < n0`)))]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* continuity *)
    X_GEN_TAC `t1:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC
     `\r. sum {i | i < n0}
            (\i. sum (pde_index_lists s (:N))
               (\l. drop(integral (interval[(cc:num->real^N) i,dd i])
                      (\y. lift(norm(iterated_partial l
                             (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                                    (pastecart (lift r) y)) y) pow 2)))))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN USE_THEN "box" MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
    X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval(a - (EE:num->real) i,b)` THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_REAL_INTERVAL] THEN
      X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
      USE_THEN "bd" (fun th -> MP_TAC(SPECL [`i:num`; `l:num list`; `r:real`] th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      USE_THEN "ext" (MP_TAC o CONJUNCT1 o C MP (ASSUME `(i:num) < n0`) o SPEC `i:num`) THEN
      UNDISCH_TAC `t1 < b` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the derivative *)
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i l. i < n0 /\ ALL (\k. 1 <= k /\ k <= dimindex(:N)) l
          ==> drop(integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
                 (\z. lift(&2 *
                   (iterated_partial l
                      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                             ((psi:num->A->real) i (chart_inv (cs i) z) %%
                              metric_local atlas (cs i) ((v:real->A->real^N^N) t) z)) z dot
                    iterated_partial l
                      (\z. partial_derivative 1
                             (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                                    (psi i (chart_inv (cs i) (sndcart w)) %%
                                     metric_local atlas (cs i)
                                       (v (drop(fstcart w))) (sndcart w)))
                             (pastecart (lift t) z)) z)))) =
              drop(integral (interval[(cc:num->real^N) i,dd i])
                 (\y. lift(&2 *
                   (iterated_partial l
                      (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                             (pastecart (lift t) y)) y dot
                    iterated_partial l
                      (\y. partial_derivative 1 (FU i) (pastecart (lift t) y)) y))))`
  (LABEL_TAC "dbox") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "cf" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    USE_THEN "ext" (fun th -> STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `(i:num) < n0`))) THEN
    SUBGOAL_THEN
     `!z. z IN IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))
          ==> partial_derivative 1
                (\w. (vectorize:real^N^N->real^(N,N)finite_prod)
                       ((psi:num->A->real) i (chart_inv (cs i) (sndcart w)) %%
                        metric_local atlas (cs i)
                          ((v:real->A->real^N^N) (drop(fstcart w))) (sndcart w)))
                (pastecart (lift t) z) =
              partial_derivative 1 ((FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i)
                (pastecart (lift t) z)`
    ASSUME_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`[1]:num list`;
        `interval(lift a,lift b) PCROSS
         IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))`;
        `\w. (vectorize:real^N^N->real^(N,N)finite_prod)
               ((psi:num->A->real) i (chart_inv ((cs:num->(A->bool)#(A->real^N)) i) (sndcart w)) %%
                metric_local atlas (cs i) ((v:real->A->real^N^N) (drop(fstcart w))) (sndcart w))`;
        `(FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i`;
        `pastecart (lift t) (z:real^N)`] TEXT_ITERATED_PARTIAL_LOCAL_AT) THEN
      REWRITE_TAC[iterated_partial] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                   LIFT_DROP] THEN
      REWRITE_TAC[FORALL_IN_PCROSS; FORALL_LIFT; IN_INTERVAL_1; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`r:real`; `y:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "fp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `integral (IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i)))
        (\y. lift(&2 *
          (iterated_partial l
             (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                    (pastecart (lift t) y)) y dot
           iterated_partial l (\y. partial_derivative 1 (FU i) (pastecart (lift t) y)) y)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THENL
       [MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
        EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN USE_THEN "fp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC TEXT_ITERATED_PARTIAL_LOCAL_AT THEN
        EXISTS_TAC `IMAGE (SND((cs:num->(A->bool)#(A->real^N)) i)) (FST(cs i))` THEN
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC PDM_INTEGRAL_SUPPORT_EQ THEN EXISTS_TAC `(ks:num->real^N->bool) i` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `iterated_partial l
          (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i (pastecart (lift t) y))
          y = vec 0`
      (fun th -> REWRITE_TAC[th; DOT_LZERO; REAL_MUL_RZERO; LIFT_NUM]) THEN
      MATCH_MP_TAC PDM_PARTIAL_ZERO_OFF THEN
      MAP_EVERY EXISTS_TAC [`(:real^N)`; `(ks:num->real^N->bool) i`] THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      USE_THEN "fz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
  EXISTS_TAC
   `\r. sum {i | i < n0}
          (\i. sum (pde_index_lists s (:N))
             (\l. drop(integral (interval[(cc:num->real^N) i,dd i])
                    (\y. lift(norm(iterated_partial l
                           (\y. (FU:num->real^(1,N)finite_sum->real^(N,N)finite_prod) i
                                  (pastecart (lift r) y)) y) pow 2)))))` THEN
  EXISTS_TAC `min (t - a) (b - t)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `r:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    USE_THEN "box" MATCH_MP_TAC THEN
    UNDISCH_TAC `abs(r - t) < min (t - a) (b - t)` THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUM THEN REWRITE_TAC[PDE_INDEX_LISTS_FINITE] THEN
  X_GEN_TAC `l:num list` THEN REWRITE_TAC[pde_index_lists; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  USE_THEN "dbox" (fun th -> REWRITE_TAC[MP (SPECL [`i:num`; `l:num list`] th)
    (CONJ (ASSUME `(i:num) < n0`)
          (ASSUME `ALL (\k. 1 <= k /\ k <= dimindex(:N)) l`))]) THEN
  USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ext" (MP_TAC o CONJUNCT1 o C MP (ASSUME `(i:num) < n0`) o SPEC `i:num`) THEN
  ASM_REAL_ARITH_TAC);;

