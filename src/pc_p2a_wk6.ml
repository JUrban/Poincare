(* ========================================================================= *)
(* Unit pc_p2a_wk6: the identity p2bw_tid of W3 (MT Cor 6.51 summed,         *)
(* Perelman (7.6)) almost everywhere on the space-time chart domain: l is    *)
(* locally Lipschitz (pc_p2a_wk2), so differentiable off a null set          *)
(* (RADEMACHER_OPEN), and at every differentiability point with a minimizer  *)
(* the pointwise identity holds (P2AW_FLOW_LX_DERIV of pc_p2a_wk3), with     *)
(* |grad l|^2 rho = p2bw_bil A l l.  Minimizer existence (FL2) is a          *)
(* hypothesis.                                                               *)
(* ========================================================================= *)

needs "src/pc_p2a_wk3.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The chart domain is open (the same fact is P2BX_CDOM_OPEN of              *)
(* pc_p2b_fchart, whose load closure contains the Prop 9.20 layer; this      *)
(* two-line copy keeps the closure of the P2A units small), almost           *)
(* everywhere differentiability of locally Lipschitz functions on an open    *)
(* set, and the bilinear expression of a gradient G X.                       *)
(* ------------------------------------------------------------------------- *)

let P2AW_CDOM_OPEN = prove
 (`!(c:(A->bool)#(A->real^N)) tmax.
     open(IMAGE (SND c) (FST c)) ==> open(p2bw_cdom c tmax)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p2bw_cdom (c:(A->bool)#(A->real^N)) tmax =
                IMAGE (SND c) (FST c) PCROSS interval(vec 0,lift tmax)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART] THEN
    REWRITE_TAC[p2bw_cdom; PASTECART_IN_PCROSS; IN_ELIM_THM; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_INTERVAL_1; DROP_VEC; LIFT_DROP];
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]]);;

let P2AW_LOCLIP_AE_DIFF = prove
 (`!(s:real^M->bool) u.
     open s /\ wan_loclip s u
     ==> negligible {x | x IN s /\ ~((\w. lift(u w)) differentiable (at x))}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_UNION_COMPACT_SUBSETS) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. ?V. open V /\ (f:num->real^M->bool) n SUBSET V /\ V SUBSET s /\
            negligible {x | x IN V /\ ~((\w. lift((u:real^M->real) w)) differentiable (at x))}`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC P2AW_LIP_NULL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:num->real^M->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\n. {x | x IN (V:num->real^M->bool) n /\
                            ~((\w. lift((u:real^M->real) w)) differentiable (at x))})
                  (:num))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    UNDISCH_TAC `UNIONS {(f:num->real^M->bool) n | n IN (:num)} = s` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2AW_QUAD_SUM = prove
 (`!(M:real^N^N) rho (u:real^N).
     sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. (rho %% M)$i$j * u$i * u$j)) =
     rho * (u dot (M ** u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dot; MATRIX_CMUL_COMPONENT; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; dot; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let P2AW_BIL_DOT = prove
 (`!(A:real^(N,1)finite_sum->real^N^N) (l:real^(N,1)finite_sum->real) z (G:real^N^N) rho X.
     invertible G /\ A z = rho %% matrix_inv G /\
     (!i. 1 <= i /\ i <= dimindex(:N) ==> wan_xder i l z = (G ** X)$i)
     ==> p2bw_bil A l l z = rho * (X dot (G ** X))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bw_bil] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. (A:real^(N,1)finite_sum->real^N^N) z$i$j *
                  wan_xder i (l:real^(N,1)finite_sum->real) z * wan_xder j l z)) =
    sum(1..dimindex(:N))
      (\i. sum(1..dimindex(:N))
             (\j. (rho %% matrix_inv G)$i$j * ((G:real^N^N) ** X)$i * (G ** X)$j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[P2AW_QUAD_SUM] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID] THEN
  AP_TERM_TAC THEN MATCH_ACCEPT_TAC DOT_SYM);;

(* ------------------------------------------------------------------------- *)
(* The identity at one differentiability point with a minimizer, and         *)
(* p2bw_tid on the chart domain given minimizers (FL2).                      *)
(* ------------------------------------------------------------------------- *)

let P2AW_LX_TID_POINT = prove
 (`!top atlas a b (g:real->A->real^3^3) p (c:(A->bool)#(A->real^3)) z (gamma:real->A).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
     z IN p2bw_cdom c (b - a) /\
     p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p (drop(sndcart z)) gamma /\
     gamma(drop(sndcart z)) = chart_inv c (fstcart z) /\
     (\w. lift(p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) w))
       differentiable (at z)
     ==> wan_tder (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                  z * p2bw_crho atlas c b g z =
         (p2bw_cscal atlas c b g z * p2bw_crho atlas c b g z -
          p2bw_bil (p2bw_cA atlas c b g)
            (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
            (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z) /
         &2 -
         p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) z /
         (&2 * drop(sndcart z)) * p2bw_crho atlas c b g z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `x = fstcart(z:real^(3,1)finite_sum)` THEN
  ABBREV_TAC `tau = drop(sndcart(z:real^(3,1)finite_sum))` THEN
  SUBGOAL_THEN `z = pastecart (x:real^3) (lift tau)` SUBST_ALL_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "tau"] THEN REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
    ALL_TAC] THEN
  UNDISCH_TAC `pastecart (x:real^3) (lift tau) IN p2bw_cdom (c:(A->bool)#(A->real^3)) (b - a)` THEN
  REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `c:(A->bool)#(A->real^3)`; `x:real^3`; `tau:real`;
                 `gamma:real->A`] P2AW_FLOW_LX_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND c) (FST c))
                  (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3)(b - tau)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`] P2AW_CBFLOW_METRICS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `b - tau` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2bw_cA atlas (c:(A->bool)#(A->real^3)) b (g:real->A->real^3^3)`;
    `p2bw_cfun (c:(A->bool)#(A->real^3))
               (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p)`;
    `pastecart (x:real^3) (lift tau)`;
    `p2bw_cmet atlas (c:(A->bool)#(A->real^3)) b (g:real->A->real^3^3) (pastecart x (lift tau))`;
    `p2bw_crho atlas (c:(A->bool)#(A->real^3)) b (g:real->A->real^3^3) (pastecart x (lift tau))`;
    `X:real^3`] P2AW_BIL_DOT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[p2bw_cA; DIMINDEX_3] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[p2bw_cmet; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    MP_TAC(ISPECL [`IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3)(b - tau))`;
                   `x:real^3`] LRG_METRIC_INVERTIBLE) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2AW_LX_TID = prove
 (`!top atlas a b (g:real->A->real^3^3) p (c:(A->bool)#(A->real^3)).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ c IN atlas /\
     (!z. z IN p2bw_cdom c (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv c (fstcart z))
     ==> p2bw_tid (p2bw_cdom c (b - a)) (p2bw_cA atlas c b g) (p2bw_crho atlas c b g)
                  (p2bw_cscal atlas c b g)
                  (p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN")))) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `c:(A->bool)#(A->real^3)`]
                P2AW_LX_LOCLIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(p2bw_cdom (c:(A->bool)#(A->real^3)) (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CDOM_OPEN THEN ASM_MESON_TAC[MFDM_CHART; P2AW_FLOW_FACTS]; ALL_TAC] THEN
  REWRITE_TAC[p2bw_tid] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `{z | z IN p2bw_cdom (c:(A->bool)#(A->real^3)) (b - a) /\
         ~((\w. lift(p2bw_cfun c (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                          (g:real->A->real^3^3)) b p) w))
           differentiable (at z))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_LOCLIP_AE_DIFF THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^(3,1)finite_sum` THEN
  ASM_CASES_TAC `(z:real^(3,1)finite_sum) IN p2bw_cdom (c:(A->bool)#(A->real^3)) (b - a)` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> ~b`) THEN DISCH_TAC THEN
  USE_THEN "MIN" (MP_TAC o SPEC `z:real^(3,1)finite_sum`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC P2AW_LX_TID_POINT THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The loclip and tid parts of W3 in its own vocabulary (rfs_flow_view, the  *)
(* hypotheses of P2B_REQ_P2A_WEAK_STATEMENT), with FL2                       *)
(* (P2A_FLOW_MIN_EXISTS_STATEMENT) as a hypothesis.                          *)
(* ------------------------------------------------------------------------- *)

let P2AW_W3_LOCLIP_TID = prove
 (`!(u:A->bool) (n:3->bool) top atlas a b (g:real->A->real^3^3) p (c:(A->bool)#(A->real^3)).
     P2A_FLOW_MIN_EXISTS_STATEMENT u n /\
     hausdorff_space top /\ connected_space top /\ a < b /\
     ricci_flow_from (top,atlas) a b g /\ rfs_flow_upto (top,atlas) a b g /\
     (!t. a <= t /\ t <= b ==> mfd_complete (top,atlas) (g t)) /\
     (?K. !t y. a <= t /\ t <= b /\ y IN topspace top ==> mfd_rm_norm atlas (g t) y <= K) /\
     p IN topspace top /\ c IN atlas
     ==> wan_loclip (p2bw_cdom c (b - a))
           (p2bw_cfun c (p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p)) /\
         p2bw_tid (p2bw_cdom c (b - a)) (p2bw_cA atlas c b g) (p2bw_crho atlas c b g)
           (p2bw_cscal atlas c b g)
           (p2bw_cfun c (p2a_lx (rfs_flow_view (top,atlas) (real_interval[a,b]) g) b p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_cbflow (top,atlas) a b (g:real->A->real^3^3)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_cbflow; P2A_FLOW_UPTO_3] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM P2A_FLOW_VIEW_3] THEN
  SUBGOAL_THEN
   `!z. z IN p2bw_cdom (c:(A->bool)#(A->real^3)) (b - a)
        ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) b p (drop(sndcart z)) gamma /\
                    gamma(drop(sndcart z)) = chart_inv c (fstcart z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[p2bw_cdom; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `P2A_FLOW_MIN_EXISTS_STATEMENT (u:A->bool) (n:3->bool)` THEN
    REWRITE_TAC[P2A_FLOW_MIN_EXISTS_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv (c:(A->bool)#(A->real^3)) (fstcart(z:real^(3,1)finite_sum)) IN FST c`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `FST(c:(A->bool)#(A->real^3))`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_LX_LOCLIP THEN EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AW_LX_TID THEN ASM_REWRITE_TAC[]]);;

