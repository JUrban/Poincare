(* ========================================================================= *)
(* Unit pc_p2a_wk7: the weak inequalities T2 and T1 of W3                    *)
(* (P2B_REQ_P2A_WEAK_STATEMENT) for a flow, given minimizers (FL2): the      *)
(* nonlinear barrier principle P2AW_NBP_MATRIX (pc_p2a_wkdec) is applied to  *)
(* l with the sharp barrier of pc_p2a_wk4 off the Sard null set and the      *)
(* non-differentiability set of l; T1 follows from T2's integral and the     *)
(* identity tid (pc_p2a_wk6) almost everywhere.  Headline P2AW_W3_FROM_FL2.  *)
(* ========================================================================= *)

needs "src/pc_p2a_wk4.ml";;
needs "src/pc_wan_lipx.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Derivatives of locally Lipschitz functions on open sets: locality of the  *)
(* Frechet derivative, measurability of directional derivatives (Kirszbraun  *)
(* extension on a compact exhaustion and WAN_LIP_DERIV_MEASURABLE) and their *)
(* bound on compact sets.                                                    *)
(* ------------------------------------------------------------------------- *)

let P2AW_FRECHET_LOCAL = prove
 (`!(f:real^M->real^N) g t x.
     open t /\ x IN t /\ (!y. y IN t ==> f y = g y)
     ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frechet_derivative] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `f':real^M->real^N` THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN THENL
   [MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `t:real^M->bool`];
    MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `t:real^M->bool`]] THEN
  ASM_SIMP_TAC[]);;

let P2AW_LOCLIP_DERIV_MEAS = prove
 (`!(s:real^M->bool) (u:real^M->real) v.
     open s /\ wan_loclip s u
     ==> (\x. lift(drop(frechet_derivative (\y. lift(u y)) (at x) v))) measurable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `f:num->real^M->bool` STRIP_ASSUME_TAC o
    MATCH_MP OPEN_UNION_COMPACT_SUBSETS) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `s:real^M->bool`)) THEN
  MATCH_MP_TAC MEASURABLE_ON_COUNTABLE_UNIONS THEN
  SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o SPEC `(f:num->real^M->bool)(n + 1)` o GEN_REWRITE_RULE I [wan_loclip]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  MP_TAC(ISPECL [`\x:real^M. lift((u:real^M->real) x)`; `(f:num->real^M->bool)(n + 1)`;
                 `max L (&0)`] KIRSZBRAUN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 <= max L (&0)`; GSYM LIFT_SUB; NORM_LIFT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * norm(x - y:real^M)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `gg:real^M->real^1` (STRIP_ASSUME_TAC o BETA_RULE))] THEN
  MATCH_MP_TAC MEASURABLE_ON_EQ THEN
  EXISTS_TAC `\x. lift(drop(frechet_derivative (gg:real^M->real^1) (at x) v))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN MATCH_MP_TAC P2AW_FRECHET_LOCAL THEN
    EXISTS_TAC `interior((f:num->real^M->bool)(n + 1))` THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
    MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_COMPACT] THEN
    MP_TAC(ISPECL [`\x. drop((gg:real^M->real^1) x)`; `max L (&0)`; `v:real^M`]
                  WAN_LIP_DERIV_MEASURABLE) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1]]);;

let P2AW_LOCLIP_DERIV_BOUND = prove
 (`!(s:real^M->bool) (u:real^M->real) k.
     open s /\ wan_loclip s u /\ compact k /\ k SUBSET s
     ==> ?C. !x v. x IN k /\ (\y. lift(u y)) differentiable (at x)
                   ==> abs(drop(frechet_derivative (\y. lift(u y)) (at x) v)) <= C * norm v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `k:real^M->bool`] WAN_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `{x + y:real^M | x IN k /\ y IN cball(vec 0,d)}` o
    REWRITE_RULE[wan_loclip]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN
  EXISTS_TAC `L:real` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC WAN_LIP_DERIV_BOUND THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(x:real^M,d) SUBSET {x + y:real^M | x IN k /\ y IN cball(vec 0,d)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^M`; `w - x:real^M`] THEN
    ASM_REWRITE_TAC[IN_CBALL_0; VECTOR_ARITH `x + w - x:real^N = w`] THEN
    ASM_MESON_TAC[NORM_SUB; dist; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

let P2AW_BIL_BOUND = prove
 (`!(A:real^N^N) (X:num->real) C.
     (!i. 1 <= i /\ i <= dimindex(:N) ==> abs(X i) <= C)
     ==> abs(sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. A$i$j * X i * X j))) <=
         C pow 2 * sum(1..dimindex(:N)) (\i. sum(1..dimindex(:N)) (\j. abs(A$i$j)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                (\i. abs(sum(1..dimindex(:N)) (\j. (A:real^N^N)$i$j * X i * X j)))` THEN
  REWRITE_TAC[SUM_ABS_NUMSEG] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\j. abs((A:real^N^N)$i$j * X i * X j))` THEN
  REWRITE_TAC[SUM_ABS_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_ABS_POS]);;


(* ------------------------------------------------------------------------- *)
(* The right-hand side Fb = (bil(A,l,l) - rho (R + (l - n)/tau)) / 2 of the  *)
(* barrier principle, made 0 where l is not differentiable (p2aw_fbar):      *)
(* measurable and bounded on compact subsets; the scalar curvature of a flow *)
(* is smooth on the space-time chart domain.                                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_FLOW_CSCAL_SMOOTH = prove
 (`!top atlas a b (g:real->A->real^3^3) U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ (U,phi) IN atlas
     ==> smooth_map_on (p2bw_cdom (U,phi) (b - a)) (\w. lift(p2bw_cscal atlas (U,phi) b g w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `U:A->bool`;
                 `phi:A->real^3`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open(p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CDOM_OPEN THEN ASM_REWRITE_TAC[FST; SND]; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_region (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) U a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CBFLOW_REGION THEN ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                 `U:A->bool`; `a:real`; `b:real`; `U:A->bool`; `phi:A->real^3`]
                P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE o MATCH_MP LRG_LSMOOTH_LSCALAR o
    MATCH_MP P2AW_LRICCI_LSMOOTH o CONJUNCT1) THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC
   `(\z. lift(lscalar (p2a_rlocal (p2a_flow_view (top,atlas) (real_interval[a,b])
                                    (g:real->A->real^3^3)) U b (U,phi) (drop(fstcart z)))
                      (sndcart z))) o
    (\w:real^(3,1)finite_sum. pastecart (lift(b - drop(sndcart w))) (fstcart w))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^(3,1)finite_sum` THEN REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FST; SND] THEN
    STRIP_TAC THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; p2bw_cscal] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`;
                   `b - drop(sndcart(w:real^(3,1)finite_sum))`;
                   `chart_inv (U,phi:A->real^3) (fstcart(w:real^(3,1)finite_sum))`]
                  P2AW_FLOW_RLOCAL_ID) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a,lift b) PCROSS IMAGE (phi:A->real^3) U` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_PCROSS THEN ASM_REWRITE_TAC[OPEN_INTERVAL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FST; SND] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\w:real^(3,1)finite_sum. lift(b - drop(sndcart w))) =
                    (\w. lift b + --(sndcart w))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; DROP_ADD; DROP_NEG; LIFT_DROP] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC P2AW_SMOOTH_SNDCART THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC P2AW_SMOOTH_FSTCART THEN ASM_REWRITE_TAC[]]]);;

let P2AW_CONT_INV_TAU = prove
 (`!(s:real^(N,1)finite_sum->bool).
     (!z. z IN s ==> &0 < drop(sndcart z))
     ==> (\z. lift(inv(drop(sndcart z)))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^(N,1)finite_sum. drop(sndcart z)`; `s:real^(N,1)finite_sum->bool`]
                CONTINUOUS_ON_INV) THEN
  REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[LINEAR_SNDCART];
    ASM_SIMP_TAC[REAL_LT_IMP_NZ]]);;

let p2aw_fbar = new_definition
 `p2aw_fbar (A:real^(N,1)finite_sum->real^N^N) (rho:real^(N,1)finite_sum->real)
            (R:real^(N,1)finite_sum->real) (l:real^(N,1)finite_sum->real)
            (z:real^(N,1)finite_sum) =
    if (\w. lift(l w)) differentiable (at z)
    then (p2bw_bil A l l z - rho z * (R z + (l z - &(dimindex(:N))) / drop(sndcart z))) / &2
    else &0`;;

let P2AW_FBAR_MEAS = prove
 (`!(s:real^(N,1)finite_sum->bool) A rho R l.
     open s /\ wan_loclip s l /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on s) /\
     (\z. lift(rho z)) continuous_on s /\ (\z. lift(R z)) continuous_on s /\
     (!z. z IN s ==> &0 < drop(sndcart z))
     ==> (\z. lift(p2aw_fbar A rho R l z)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lebesgue_measurable(s:real^(N,1)finite_sum->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^(N,1)finite_sum->real^1. f continuous_on s ==> f measurable_on s`
  (LABEL_TAC "CM") THENL
   [ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE) THEN
  EXISTS_TAC `\z:real^(N,1)finite_sum.
                inv(&2) % (lift(p2bw_bil (A:real^(N,1)finite_sum->real^N^N) l l z) -
                           lift(rho z * (R z + (l z - &(dimindex(:N))) *
                                                inv(drop(sndcart z)))))` THEN
  EXISTS_TAC `{z:real^(N,1)finite_sum | z IN s /\ ~((\w. lift(l w)) differentiable (at z))}` THEN
  ASM_SIMP_TAC[P2AW_LOCLIP_AE_DIFF] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^(N,1)finite_sum` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(\w. lift((l:real^(N,1)finite_sum->real) w)) differentiable (at z)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[p2aw_fbar; GSYM LIFT_SUB; GSYM LIFT_CMUL; LIFT_EQ; real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_CMUL THEN MATCH_MP_TAC MEASURABLE_ON_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[p2bw_bil; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC MEASURABLE_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC MEASURABLE_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC THENL
     [USE_THEN "CM" MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN REWRITE_TAC[wan_xder] THEN
    ASM_SIMP_TAC[P2AW_LOCLIP_DERIV_MEAS];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC THENL
   [USE_THEN "CM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN CONJ_TAC THENL
   [USE_THEN "CM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC THEN USE_THEN "CM" MATCH_MP_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
    MATCH_MP_TAC P2AW_CONT_INV_TAU THEN ASM_REWRITE_TAC[]]);;

let P2AW_FBAR_ARITH = prove
 (`!b r R0 l0 t n Kb Br BR Bl Bi.
     abs b <= Kb /\ abs r <= Br /\ abs R0 <= BR /\ abs l0 <= Bl /\ abs(inv t) <= Bi /\
     &0 <= n
     ==> abs((b - r * (R0 + (l0 - n) / t)) / &2) <= (Kb + Br * (BR + (Bl + n) * Bi)) / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(R0 + (l0 - n) / t) <= BR + (Bl + n) * Bi` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs a <= A /\ abs c <= C ==> abs(a + c) <= A + C`) THEN
    ASM_REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(r * (R0 + (l0 - n) / t)) <= Br * (BR + (Bl + n) * Bi)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let P2AW_FBAR_BOUND = prove
 (`!(s:real^(N,1)finite_sum->bool) A rho R l k.
     open s /\ wan_loclip s l /\
     (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
            ==> (\z. lift(A z$i$j)) continuous_on s) /\
     (\z. lift(rho z)) continuous_on s /\ (\z. lift(R z)) continuous_on s /\
     (!z. z IN s ==> &0 < drop(sndcart z)) /\ compact k /\ k SUBSET s
     ==> ?C. !z. z IN k ==> abs(p2aw_fbar A rho R l z) <= C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^(N,1)finite_sum->bool`; `l:real^(N,1)finite_sum->real`;
                 `k:real^(N,1)finite_sum->bool`] P2AW_LOCLIP_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Cd:real`) THEN
  SUBGOAL_THEN
   `!f:real^(N,1)finite_sum->real.
      (\z. lift(f z)) continuous_on s ==> ?B. &0 <= B /\ !z. z IN k ==> abs(f z) <= B`
  (LABEL_TAC "CB") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_CONT_BOUND THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  USE_THEN "CB" (MP_TAC o SPEC `rho:real^(N,1)finite_sum->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `Br:real` STRIP_ASSUME_TAC)] THEN
  USE_THEN "CB" (MP_TAC o SPEC `R:real^(N,1)finite_sum->real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `BR:real` STRIP_ASSUME_TAC)] THEN
  USE_THEN "CB" (MP_TAC o SPEC `l:real^(N,1)finite_sum->real`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[WAN_LOCLIP_CONTINUOUS_ON]; DISCH_THEN(X_CHOOSE_THEN `Bl:real` STRIP_ASSUME_TAC)] THEN
  USE_THEN "CB" (MP_TAC o SPEC `\z:real^(N,1)finite_sum. inv(drop(sndcart z))`) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN ASM_SIMP_TAC[P2AW_CONT_INV_TAU];
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `Bi:real` STRIP_ASSUME_TAC)] THEN
  USE_THEN "CB" (MP_TAC o SPEC
    `\z:real^(N,1)finite_sum. sum(1..dimindex(:N))
       (\i. sum(1..dimindex(:N)) (\j. abs((A:real^(N,1)finite_sum->real^N^N) z$i$j)))`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN ASM_SIMP_TAC[];
    BETA_TAC THEN DISCH_THEN(X_CHOOSE_THEN `Ba:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `(max Cd (&0) pow 2 * Ba + Br * (BR + (Bl + &(dimindex(:N))) * Bi)) / &2` THEN
  X_GEN_TAC `z:real^(N,1)finite_sum` THEN DISCH_TAC THEN REWRITE_TAC[p2aw_fbar] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_ABS_NUM] THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[REAL_POS]]] THEN
  MATCH_MP_TAC P2AW_FBAR_ARITH THEN ASM_SIMP_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `max Cd (&0) pow 2 *
              sum(1..dimindex(:N))
                (\i. sum(1..dimindex(:N)) (\j. abs((A:real^(N,1)finite_sum->real^N^N) z$i$j)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2bw_bil] THEN
    MP_TAC(ISPECL [`(A:real^(N,1)finite_sum->real^N^N) z`;
                   `\i. wan_xder i (l:real^(N,1)finite_sum->real) z`; `max Cd (&0)`]
                  P2AW_BIL_BOUND) THEN
    BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Cd * &1` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `norm(pastecart (basis i:real^N) (vec 0:real^1)) = &1`
        (fun th -> REWRITE_TAC[GSYM th]) THENL
       [ASM_SIMP_TAC[NORM_PASTECART_0; NORM_BASIS]; ALL_TAC] THEN
      REWRITE_TAC[wan_xder] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(N,1)finite_sum` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Ba:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The barrier principle P2AW_NBP_MATRIX for l = p2a_lx in a chart (U,phi)   *)
(* of a flow, given minimizers: the sharp barrier P2AW_FLOW_SHARP_BARRIER    *)
(* holds off the union of the non-differentiability set of l (Rademacher)    *)
(* and the Sard set of P2AW_FLOW_CONJ_NULL.                                  *)
(* ------------------------------------------------------------------------- *)

let P2AW_LX_NBP = prove
 (`!top atlas a b (g:real->A->real^3^3) p U (phi:A->real^3) phi0.
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!z. z IN p2bw_cdom (U,phi) (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z)) /\
     wan_test (p2bw_cdom (U,phi) (b - a)) phi0 /\ (!z. &0 <= phi0 z)
     ==> (\z. lift(phi0 z *
                   p2aw_fbar (p2bw_cA atlas (U,phi) b g) (p2bw_crho atlas (U,phi) b g)
                     (p2bw_cscal atlas (U,phi) b g)
                     (p2bw_cfun (U,phi)
                        (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z))
           integrable_on p2bw_cdom (U,phi) (b - a) /\
         (\z. lift(p2bw_bil (p2bw_cA atlas (U,phi) b g)
                     (p2bw_cfun (U,phi)
                        (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                     phi0 z))
           integrable_on p2bw_cdom (U,phi) (b - a) /\
         &0 <= drop(integral (p2bw_cdom (U,phi) (b - a))
                  (\z. lift(phi0 z *
                            p2aw_fbar (p2bw_cA atlas (U,phi) b g) (p2bw_crho atlas (U,phi) b g)
                              (p2bw_cscal atlas (U,phi) b g)
                              (p2bw_cfun (U,phi)
                                 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p)) z))) +
               drop(integral (p2bw_cdom (U,phi) (b - a))
                  (\z. lift(p2bw_bil (p2bw_cA atlas (U,phi) b g)
                              (p2bw_cfun (U,phi)
                                 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                         b p))
                              phi0 z)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2AW_FLOW_FACTS) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  SUBGOAL_THEN `p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a,b])
                           (g:real->A->real^3^3)) b = top` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (p2a_flow_view (top,atlas) (real_interval[a,b])
                              (g:real->A->real^3^3)) p b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `(U:A->bool,phi:A->real^3)`]
                P2AW_LX_LOCLIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `(U:A->bool,phi:A->real^3)`]
                P2AW_LX_SEMICONC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`] P2AW_FLOW_CA_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `U:A->bool`; `phi:A->real^3`] P2AW_FLOW_CSCAL_SMOOTH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `open(p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CDOM_OPEN THEN REWRITE_TAC[FST; SND] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `U:A->bool`; `phi:A->real^3`]
                P2AW_FLOW_CONJ_NULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nb:real^(3,1)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(!i j. 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
           ==> (\z. lift(p2bw_cA atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3) z$i$j))
               continuous_on p2bw_cdom (U,phi) (b - a)) /\
    (\z. lift(p2bw_crho atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3) z))
      continuous_on p2bw_cdom (U,phi) (b - a) /\
    (\z. lift(p2bw_cscal atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3) z))
      continuous_on p2bw_cdom (U,phi) (b - a) /\
    (!z. z IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a) ==> &0 < drop(sndcart z)) /\
    (!i j. 1 <= i /\ i <= dimindex(:3) /\ 1 <= j /\ j <= dimindex(:3)
           ==> smooth_map_on (p2bw_cdom (U,phi) (b - a))
                 (\z. lift(p2bw_cA atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3)
                             z$i$j))) /\
    (!y. y IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)
         ==> symmetric_matrix(p2bw_cA atlas (U,phi) b (g:real->A->real^3^3) y) /\
             !v. ~(v = vec 0) ==> &0 < v dot (p2bw_cA atlas (U,phi) b g y ** v))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      SIMP_TAC[p2bw_cdom; IN_ELIM_THM];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`;
    `p2bw_cA atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3)`;
    `p2bw_crho atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3)`;
    `p2bw_cscal atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3)`;
    `p2bw_cfun (U:A->bool,phi:A->real^3)
       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p)`]
   P2AW_FBAR_MEAS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!kk. compact kk /\ kk SUBSET p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)
         ==> ?C. !x. x IN kk
                     ==> abs(p2aw_fbar (p2bw_cA atlas (U,phi) b (g:real->A->real^3^3))
                               (p2bw_crho atlas (U,phi) b g) (p2bw_cscal atlas (U,phi) b g)
                               (p2bw_cfun (U,phi)
                                  (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g)
                                          b p)) x) <= C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2AW_FBAR_BOUND THEN
    EXISTS_TAC `p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)`;
    `p2bw_cA atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3)`;
    `p2bw_cfun (U:A->bool,phi:A->real^3)
       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p)`;
    `p2aw_fbar (p2bw_cA atlas (U:A->bool,phi:A->real^3) b (g:real->A->real^3^3))
       (p2bw_crho atlas (U,phi) b g) (p2bw_cscal atlas (U,phi) b g)
       (p2bw_cfun (U,phi) (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))`;
    `phi0:real^(3,1)finite_sum->real`] P2AW_NBP_MATRIX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXISTS_TAC
     `{z:real^(3,1)finite_sum |
         z IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a) /\
         ~((\w. lift(p2bw_cfun (U,phi)
                       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) b p) w)) differentiable (at z))}
      UNION Nb` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2AW_LOCLIP_AE_DIFF THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `((\w. lift(p2bw_cfun (U:A->bool,phi:A->real^3)
                  (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                             (g:real->A->real^3^3)) b p) w)) differentiable (at z)) /\
      ~((z:real^(3,1)finite_sum) IN Nb)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `fstcart(z:real^(3,1)finite_sum) IN IMAGE (phi:A->real^3) U /\
                  &0 < drop(sndcart z) /\ drop(sndcart z) < b - a` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN
      REWRITE_TAC[p2bw_cdom; IN_ELIM_THM; FST; SND];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^(3,1)finite_sum` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_min")) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_inv")) (concl th) &&
      not (can (find_term ((=) `Nb:real^(3,1)finite_sum->bool`)) (concl th)))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gamma:real->A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)`;
                   `b:real`; `p:A`; `drop(sndcart(z:real^(3,1)finite_sum))`; `gamma:real->A`]
                  P2A_MIN_LGEOD_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `Z0:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `Z0 IN p2a_Smin (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
                     (drop(sndcart(z:real^(3,1)finite_sum)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AW_SMIN_OF_MIN THEN EXISTS_TAC `gamma:real->A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < p2a_J (p2a_flow_view (top,atlas) (real_interval[a,b]) (g:real->A->real^3^3)) b p
                 (drop(sndcart(z:real^(3,1)finite_sum))) Z0`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Nb:real^(3,1)finite_sum->bool`)) (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`fstcart(z:real^(3,1)finite_sum)`; `gamma:real->A`] THEN
      ASM_REWRITE_TAC[LIFT_DROP; PASTECART_FST_SND];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                   `g:real->A->real^3^3`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                   `z:real^(3,1)finite_sum`; `gamma:real->A`; `Z0:real^3`]
                  P2AW_FLOW_SHARP_BARRIER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:real^(3,1)finite_sum->real`
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) o REWRITE_RULE[DIMINDEX_3]) THEN
    MAP_EVERY EXISTS_TAC [`psi:real^(3,1)finite_sum->real`; `r:real`] THEN
    ASM_REWRITE_TAC[p2aw_fbar; DIMINDEX_3];
    REWRITE_TAC[p2bw_bil] THEN DISCH_THEN ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* T2 and T1 (p2bw_t2, p2bw_t1) in a chart of a flow, given minimizers.  Off *)
(* the non-differentiability set of l the T2 integrand is -2 (phi Fb +       *)
(* bil(A,l,phi)); off that set and the tid exceptional set the T1 integrand  *)
(* is phi Fb + bil(A,l,phi).                                                 *)
(* ------------------------------------------------------------------------- *)

let P2AW_LX_T2 = prove
 (`!top atlas a b (g:real->A->real^3^3) p U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!z. z IN p2bw_cdom (U,phi) (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z))
     ==> p2bw_t2 (p2bw_cdom (U,phi) (b - a)) (p2bw_cA atlas (U,phi) b g)
                 (p2bw_crho atlas (U,phi) b g) (p2bw_cscal atlas (U,phi) b g)
                 (p2bw_cfun (U,phi)
                    (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_t2] THEN
  X_GEN_TAC `phi0:real^(3,1)finite_sum->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `phi0:real^(3,1)finite_sum->real`] P2AW_LX_NBP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `(U:A->bool,phi:A->real^3)`]
                P2AW_LX_LOCLIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `open(p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CDOM_OPEN THEN REWRITE_TAC[FST; SND] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; P2AW_FLOW_FACTS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))
      (\z. lift(phi0 z *
                (--(p2bw_bil (p2bw_cA atlas (U,phi) b (g:real->A->real^3^3))
                      (p2bw_cfun (U,phi)
                         (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                      (p2bw_cfun (U,phi)
                         (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z) +
                 (p2bw_cscal atlas (U,phi) b g z +
                  (p2bw_cfun (U,phi)
                     (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) z -
                   &(dimindex(:3))) / drop(sndcart z)) * p2bw_crho atlas (U,phi) b g z) -
                &2 * p2bw_bil (p2bw_cA atlas (U,phi) b g)
                       (p2bw_cfun (U,phi)
                          (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                       phi0 z)) =
    --(&2) %
    (integral (p2bw_cdom (U,phi) (b - a))
       (\z. lift(phi0 z *
                 p2aw_fbar (p2bw_cA atlas (U,phi) b g) (p2bw_crho atlas (U,phi) b g)
                   (p2bw_cscal atlas (U,phi) b g)
                   (p2bw_cfun (U,phi)
                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z)) +
     integral (p2bw_cdom (U,phi) (b - a))
       (\z. lift(p2bw_bil (p2bw_cA atlas (U,phi) b g)
                   (p2bw_cfun (U,phi)
                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                   phi0 z)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM INTEGRAL_ADD; GSYM INTEGRAL_CMUL; INTEGRABLE_ADD] THEN
    MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{z:real^(3,1)finite_sum |
         z IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a) /\
         ~((\w. lift(p2bw_cfun (U,phi)
                       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) b p) w)) differentiable (at z))}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2AW_LOCLIP_AE_DIFF THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(\w. lift(p2bw_cfun (U:A->bool,phi:A->real^3)
                 (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                            (g:real->A->real^3^3)) b p) w)) differentiable (at z)`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[p2aw_fbar; GSYM LIFT_ADD; GSYM LIFT_CMUL; LIFT_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DROP_CMUL; DROP_ADD] THEN ASM_REAL_ARITH_TAC);;

let P2AW_LX_T1 = prove
 (`!top atlas a b (g:real->A->real^3^3) p U (phi:A->real^3).
     p2a_cbflow (top,atlas) a b g /\ p IN topspace top /\ (U,phi) IN atlas /\
     (!z. z IN p2bw_cdom (U,phi) (b - a)
          ==> ?gamma. p2a_min (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p
                              (drop(sndcart z)) gamma /\
                      gamma(drop(sndcart z)) = chart_inv (U,phi) (fstcart z))
     ==> p2bw_t1 (p2bw_cdom (U,phi) (b - a)) (p2bw_cA atlas (U,phi) b g)
                 (p2bw_crho atlas (U,phi) b g) (p2bw_cscal atlas (U,phi) b g)
                 (p2bw_cfun (U,phi)
                    (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bw_t1] THEN
  X_GEN_TAC `phi0:real^(3,1)finite_sum->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `U:A->bool`; `phi:A->real^3`;
                 `phi0:real^(3,1)finite_sum->real`] P2AW_LX_NBP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `m:real` o MATCH_MP P2AW_CBFLOW_SCAL_LOWER) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `m:real`; `p:A`; `(U:A->bool,phi:A->real^3)`]
                P2AW_LX_LOCLIP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `open(p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AW_CDOM_OPEN THEN REWRITE_TAC[FST; SND] THEN
    ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART; P2AW_FLOW_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `(U:A->bool,phi:A->real^3)`] P2AW_LX_TID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[p2bw_tid] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `integral (p2bw_cdom (U:A->bool,phi:A->real^3) (b - a))
      (\z. lift(phi0 z *
                (wan_tder (p2bw_cfun (U,phi)
                             (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                        (g:real->A->real^3^3)) b p)) z *
                 p2bw_crho atlas (U,phi) b g z +
                 p2bw_bil (p2bw_cA atlas (U,phi) b g)
                   (p2bw_cfun (U,phi)
                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                   (p2bw_cfun (U,phi)
                      (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z +
                 (&(dimindex(:3)) / (&2 * drop(sndcart z)) - p2bw_cscal atlas (U,phi) b g z) *
                 p2bw_crho atlas (U,phi) b g z) +
                p2bw_bil (p2bw_cA atlas (U,phi) b g)
                  (p2bw_cfun (U,phi)
                     (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                  phi0 z)) =
    integral (p2bw_cdom (U,phi) (b - a))
      (\z. lift(phi0 z *
                p2aw_fbar (p2bw_cA atlas (U,phi) b g) (p2bw_crho atlas (U,phi) b g)
                  (p2bw_cscal atlas (U,phi) b g)
                  (p2bw_cfun (U,phi)
                     (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z)) +
    integral (p2bw_cdom (U,phi) (b - a))
      (\z. lift(p2bw_bil (p2bw_cA atlas (U,phi) b g)
                  (p2bw_cfun (U,phi)
                     (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                  phi0 z))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM INTEGRAL_ADD] THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC
     `{z:real^(3,1)finite_sum |
         z IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a) /\
         ~((\w. lift(p2bw_cfun (U,phi)
                       (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                                  (g:real->A->real^3^3)) b p) w)) differentiable (at z))} UNION
      {z | z IN p2bw_cdom (U,phi) (b - a) /\
           ~(wan_tder (p2bw_cfun (U,phi)
                         (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z *
             p2bw_crho atlas (U,phi) b g z =
             (p2bw_cscal atlas (U,phi) b g z * p2bw_crho atlas (U,phi) b g z -
              p2bw_bil (p2bw_cA atlas (U,phi) b g)
                (p2bw_cfun (U,phi)
                   (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
                (p2bw_cfun (U,phi)
                   (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z) / &2 -
             p2bw_cfun (U,phi)
               (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) z /
             (&2 * drop(sndcart z)) * p2bw_crho atlas (U,phi) b g z)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2AW_LOCLIP_AE_DIFF THEN ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^(3,1)finite_sum` THEN REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `((\w. lift(p2bw_cfun (U:A->bool,phi:A->real^3)
                  (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b])
                             (g:real->A->real^3^3)) b p) w)) differentiable (at z)) /\
      wan_tder (p2bw_cfun (U,phi)
                  (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z *
      p2bw_crho atlas (U,phi) b g z =
      (p2bw_cscal atlas (U,phi) b g z * p2bw_crho atlas (U,phi) b g z -
       p2bw_bil (p2bw_cA atlas (U,phi) b g)
         (p2bw_cfun (U,phi)
            (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p))
         (p2bw_cfun (U,phi)
            (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p)) z) / &2 -
      p2bw_cfun (U,phi)
        (p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,b]) g) b p) z /
      (&2 * drop(sndcart z)) * p2bw_crho atlas (U,phi) b g z`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < drop(sndcart(z:real^(3,1)finite_sum))` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^(3,1)finite_sum) IN p2bw_cdom (U:A->bool,phi:A->real^3) (b - a)` THEN
      SIMP_TAC[p2bw_cdom; IN_ELIM_THM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[p2aw_fbar; GSYM LIFT_ADD; LIFT_EQ] THEN
    UNDISCH_TAC `&0 < drop(sndcart(z:real^(3,1)finite_sum))` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[DROP_ADD] THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* W3 (P2B_REQ_P2A_WEAK_STATEMENT) from FL2 (P2A_FLOW_MIN_EXISTS_STATEMENT): *)
(* loclip and tid from pc_p2a_wk6, T1 and T2 from the previous section, in   *)
(* W3's vocabulary (rfs_flow_view, any chart c).                             *)
(* ------------------------------------------------------------------------- *)

let P2AW_W3_FROM_FL2 = prove
 (`!(u:A->bool) (n:3->bool).
     P2A_FLOW_MIN_EXISTS_STATEMENT u n ==> P2B_REQ_P2A_WEAK_STATEMENT u`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[P2B_REQ_P2A_WEAK_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                       `b:real`; `g:real->A->real^3^3`; `p:A`; `c:(A->bool)#(A->real^3)`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `n:3->bool`; `top:A topology`;
                 `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `p:A`; `c:(A->bool)#(A->real^3)`]
                P2AW_W3_LOCLIP_TID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
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
  MP_TAC(ISPEC `c:(A->bool)#(A->real^3)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^3`] THEN DISCH_THEN SUBST_ALL_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2AW_LX_T1 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AW_LX_T2 THEN ASM_REWRITE_TAC[]]);;


