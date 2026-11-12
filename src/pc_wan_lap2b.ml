(* ========================================================================= *)
(* pc_wan_lap2b: the radial mean value property of harmonic functions for    *)
(* the mollifier wan_mke, interior derivative estimates, WAN_WEYL and        *)
(* WAN_HARM_GRAD_OSC, in every dimension.                                    *)
(*   - the profile of wan_mk and the radial potential P with                 *)
(*     grad P(z) = wan_mk z % z, compactly supported in cball(0,1);          *)
(*   - the radial mean value property: for v harmonic near cball(x,d),       *)
(*     wan_moll d v x = v x (the mean M(rho) of v(x - rho z) against         *)
(*     wan_mk has derivative rho int P (Lap v)(x - rho z) = 0);              *)
(*   - Laplacians of convolutions and mollifications of weakly harmonic      *)
(*     functions;                                                            *)
(*   - WAN_WEYL;                                                             *)
(*   - interior derivative estimates and WAN_HARM_GRAD_OSC.                  *)
(* ========================================================================= *)

needs "src/pc_wan_p4defs.ml";;
needs "src/pc_wan_moll.ml";;
needs "src/pc_wan_preg.ml";;
needs "src/pc_wan_lap2a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The profile wanl_prof of the bump smooth_bump (1/2) 1, its                *)
(* primitive wanl_phi (zero on [1,inf)), and the radial potential            *)
(* z |-> wanl_phi(|z|^2) whose gradient is wanl_prof(|z|^2) z.               *)
(* ========================================================================= *)

let wanl_prof = new_definition
 `wanl_prof s = smooth_step((&1 - s) / (&3 / &4))`;;

let wanl_phi = new_definition
 `wanl_phi t = inv(&2) * (real_integral (real_interval[--(&1),t]) wanl_prof -
                          real_integral (real_interval[--(&1),&1]) wanl_prof)`;;

let WANL_BUMP_PROFILE = prove
 (`!z:real^N. smooth_bump (&1 / &2) (&1) z = wanl_prof(norm z pow 2)`,
  GEN_TAC THEN REWRITE_TAC[smooth_bump; wanl_prof] THEN AP_TERM_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ONE]);;

let WANL_PROF_SMOOTH = prove
 (`smooth_map_on (:real^1) (\t. lift(wanl_prof(drop t)))`,
  REWRITE_TAC[wanl_prof] THEN
  SUBGOAL_THEN
   `(\t:real^1. lift(smooth_step((&1 - drop t) / (&3 / &4)))) =
    (\t. lift(smooth_step(drop((\t:real^1. lift(&4 / &3) - (&4 / &3) % t) t))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; DROP_SUB; DROP_CMUL; LIFT_DROP] THEN GEN_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]);;

let WANL_PROF_ZERO = prove
 (`!s. &1 <= s ==> wanl_prof s = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_prof] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= --x * y ==> x * y <= &0`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let WANL_PROF_POS = prove
 (`!s. &0 <= wanl_prof s`,
  REWRITE_TAC[wanl_prof; SMOOTH_STEP_BOUNDS]);;

let WANL_PROF_CONTINUOUS = prove
 (`!s. wanl_prof real_continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
  REWRITE_TAC[SUBSET_UNIV; REAL_CONTINUOUS_ON; IMAGE_LIFT_UNIV] THEN
  MP_TAC(MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON WANL_PROF_SMOOTH) THEN
  REWRITE_TAC[o_DEF]);;

let WANL_PHI_DERIV = prove
 (`!t. --(&1) < t ==> (wanl_phi has_real_derivative (inv(&2) * wanl_prof t)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\u. real_integral (real_interval[--(&1),u]) wanl_prof) has_real_derivative
     wanl_prof t) (atreal t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`wanl_prof`; `--(&1)`; `t + &1`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
    REWRITE_TAC[WANL_PROF_CONTINUOUS] THEN DISCH_THEN(MP_TAC o SPEC `t:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\u. real_integral (real_interval[--(&1),u]) wanl_prof`;
                   `wanl_prof t`; `t:real`; `real_interval(--(&1),t + &1)`]
           HAS_REAL_DERIVATIVE_WITHIN_REAL_OPEN) THEN
    REWRITE_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `real_interval[--(&1),t + &1]` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `wanl_phi = (\t. inv(&2) * (real_integral (real_interval[--(&1),t]) wanl_prof -
                               real_integral (real_interval[--(&1),&1]) wanl_prof))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wanl_phi]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `x = x - &0`] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST]);;

let WANL_PHI_OPEN = prove
 (`open {t:real^1 | --(&1) < drop t}`,
  REWRITE_TAC[drop; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT]);;

let WANL_PHI_SMOOTH = prove
 (`smooth_map_on {t:real^1 | --(&1) < drop t} (\t. lift(wanl_phi(drop t)))`,
  SUBGOAL_THEN
   `!m. continuously_differentiable (SUC m) {t:real^1 | --(&1) < drop t}
          (\t. lift(wanl_phi(drop t)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\t:real^1. lift(wanl_phi(drop t))) = lift o wanl_phi o drop`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUC_REAL_1D THEN
    EXISTS_TAC `\t. inv(&2) * wanl_prof t` THEN REWRITE_TAC[WANL_PHI_OPEN] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC WANL_PHI_DERIV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on {t:real^1 | --(&1) < drop t} (lift o (\t. inv(&2) * wanl_prof t) o drop)`
    MP_TAC THENL
     [SUBGOAL_THEN `(lift o (\t. inv(&2) * wanl_prof t) o drop) =
                    (\t:real^1. inv(&2) % lift(wanl_prof(drop t)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_CMUL]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[WANL_PHI_OPEN] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[SUBSET_UNIV; WANL_PROF_SMOOTH];
      SIMP_TAC[smooth_map_on]];
    ALL_TAC] THEN
  REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_MONO THEN EXISTS_TAC `SUC n` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WANL_PHI_ZERO = prove
 (`!t. &1 <= t ==> wanl_phi t = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wanl_phi] THEN
  MP_TAC(ISPECL [`wanl_prof`; `--(&1)`; `t:real`; `&1`] REAL_INTEGRAL_COMBINE) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; WANL_PROF_CONTINUOUS] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `real_integral (real_interval[&1,t]) wanl_prof = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `real_integral (real_interval[&1,t]) (\s. &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_EQ THEN SIMP_TAC[IN_REAL_INTERVAL; WANL_PROF_ZERO];
      REWRITE_TAC[REAL_INTEGRAL_0]];
    REAL_ARITH_TAC]);;

(* The radial potential z |-> wanl_phi(|z|^2).                              *)

let WANL_RADIAL_SMOOTH = prove
 (`smooth_map_on (:real^N) (\z:real^N. lift(wanl_phi(norm z pow 2)))`,
  SUBGOAL_THEN `(\z:real^N. lift(wanl_phi(norm z pow 2))) =
                (\t. lift(wanl_phi(drop t))) o (\z. lift(norm z pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{t:real^1 | --(&1) < drop t}` THEN
  REWRITE_TAC[OPEN_UNIV; WANL_PHI_OPEN; WANL_PHI_SMOOTH] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; LIFT_DROP] THEN
    MESON_TAC[REAL_LE_POW_2; REAL_ARITH `&0 <= x ==> --(&1) < x`];
    MP_TAC(ISPECL [`(:real^N)`; `\z:real^N. z`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID]]);;

let WANL_RADIAL_ZERO = prove
 (`!z:real^N. &1 <= norm z ==> wanl_phi(norm z pow 2) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_PHI_ZERO THEN
  MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x ==> &1 <= x`) THEN
  REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let WANL_RADIAL_FD = prove
 (`!(z:real^N) h.
        frechet_derivative (\z. lift(wanl_phi(norm z pow 2))) (at z) h =
        lift(wanl_prof(norm z pow 2) * (z dot h))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `((\z:real^N. lift(wanl_phi(norm z pow 2))) has_derivative
     (\h. lift(wanl_prof(norm z pow 2) * (z dot h)))) (at z)`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  SUBGOAL_THEN `(\z:real^N. lift(wanl_phi(norm z pow 2))) =
                (lift o wanl_phi o drop) o (\z. lift(norm z pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\h:real^N. lift(wanl_prof(norm z pow 2) * (z dot h))) =
    (\x. (inv(&2) * wanl_prof(norm z pow 2)) % x) o (\x. &2 % lift(z dot x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL] THEN
    GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT] THEN
  REWRITE_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT] THEN
  MATCH_MP_TAC WANL_PHI_DERIV THEN
  MP_TAC(SPEC `norm(z:real^N)` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

(* The kernel and its radial potential: grad wanl_pot = wan_mk z % z.        *)

let wanl_pot = new_definition
 `wanl_pot (z:real^N) =
    wanl_phi(norm z pow 2) /
    drop(integral (:real^N) (\y. lift(smooth_bump (&1 / &2) (&1) y)))`;;

let WANL_MK_PROFILE = prove
 (`!z:real^N. wan_mk z =
              wanl_prof(norm z pow 2) /
              drop(integral (:real^N) (\y. lift(smooth_bump (&1 / &2) (&1) y)))`,
  REWRITE_TAC[wan_mk; WANL_BUMP_PROFILE]);;

let WANL_POT_SMOOTH = prove
 (`smooth_map_on (:real^N) (\z:real^N. lift(wanl_pot z))`,
  REWRITE_TAC[wanl_pot; real_div; REAL_MUL_SYM; LIFT_CMUL] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; WANL_RADIAL_SMOOTH]);;

let WANL_POT_ZERO = prove
 (`!z:real^N. &1 <= norm z ==> wanl_pot z = &0`,
  SIMP_TAC[wanl_pot; WANL_RADIAL_ZERO; real_div; REAL_MUL_LZERO]);;

let WANL_POT_FD = prove
 (`!(z:real^N) h.
        frechet_derivative (\z. lift(wanl_pot z)) (at z) h = lift(wan_mk z * (z dot h))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `c = drop(integral (:real^N) (\y. lift(smooth_bump (&1 / &2) (&1) y)))` THEN
  SUBGOAL_THEN
   `((\z:real^N. lift(wanl_pot z)) has_derivative
     (\h. inv c % lift(wanl_prof(norm z pow 2) * (z dot h)))) (at z)`
  MP_TAC THENL
   [SUBGOAL_THEN `(\z:real^N. lift(wanl_pot z)) =
                  (\z. inv c % lift(wanl_phi(norm z pow 2)))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; wanl_pot; real_div; GSYM LIFT_CMUL] THEN
      REWRITE_TAC[REAL_MUL_SYM];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
    MP_TAC(ISPEC `z:real^N` WANL_RADIAL_FD) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV; WANL_RADIAL_SMOOTH];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  ASM_REWRITE_TAC[WANL_MK_PROFILE; GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The radial mean value property for the mollifier wan_mke.                 *)
(* ========================================================================= *)

let WANL_CBALL_EXPAND = prove
 (`!(U:real^N->bool) x d.
        open U /\ cball(x,d) SUBSET U ==> ?d2. d < d2 /\ cball(x,d2) SUBSET U`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d < &0` THENL
   [EXISTS_TAC `d / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cball(x:real^N,d / &2) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[CBALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[EMPTY_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(x:real^N,d)`; `(:real^N) DIFF U`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; GSYM OPEN_CLOSED] THEN ANTS_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d + e / &2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `dist(x:real^N,y) <= d` THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN ASM_REWRITE_TAC[IN_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `D = dist(x:real^N,y)` THEN
  SUBGOAL_THEN `&0 < D /\ d < D` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x + (d / D) % (y - x):real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[IN_CBALL] THEN
  SUBGOAL_THEN `norm(y - x:real^N) = D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d / D /\ d / D < &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LT_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + y) = norm y`] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(x + c % (y - x)) - y:real^N = (c - &1) % (y - x)`] THEN
  ASM_REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> abs c = c`; REAL_ARITH `c < &1 ==> abs(c - &1) = &1 - c`] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_SUB_RDISTRIB; REAL_MUL_LID] THEN
  ASM_REAL_ARITH_TAC);;

let WANL_HARMONIC_EXTEND = prove
 (`!(U:real^N->bool) (v:real^N->real) x d.
        open U /\ smooth_map_on U (\y. lift(v y)) /\
        (!y. y IN U ==> llap (\z:real^N. mat 1) v y = &0) /\
        cball(x,d) SUBSET U
        ==> ?w d1. d < d1 /\ smooth_map_on (:real^N) (\y. lift(w y)) /\
                   (!y. y IN ball(x,d1) ==> w y = v y) /\
                   (!y. y IN ball(x,d1) ==> llap (\z:real^N. mat 1) w y = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `x:real^N`; `d:real`] WANL_CBALL_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `a = (&2 * d + d2) / &3` THEN ABBREV_TAC `b = (d + &2 * d2) / &3` THEN
  SUBGOAL_THEN `d < a /\ a < b /\ b < d2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= a` THENL [ALL_TAC;
    (* then cball(x,d) is empty: any smooth extension works *)
    EXISTS_TAC `\y:real^N. &0` THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; LIFT_NUM] THEN
    SUBGOAL_THEN `ball(x:real^N,a) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[NOT_IN_EMPTY]]] THEN
  EXISTS_TAC `\y:real^N. if y IN U then smooth_bump a b (y - x) * v y else &0` THEN
  EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ball(x:real^N,a) SUBSET U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^N,d2)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(x:real^N,a)
        ==> (if y IN U then smooth_bump a b (y - x) * v y else &0) = v y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN U` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_RING `c = &1 ==> c * v = v`) THEN
    MATCH_MP_TAC SMOOTH_BUMP_1 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN ball(x,a)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`] NORM_SUB) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `y:real^N` THEN ASM_CASES_TAC `(y:real^N) IN U` THENL
     [EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC WANL_SMOOTH_MAP_ON_EQ THEN
      EXISTS_TAC `\y:real^N. lift(smooth_bump a b (y - x) * v y)` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      SUBGOAL_THEN `(\y:real^N. lift(smooth_bump a b (y - x))) =
                    (\y. lift(smooth_bump a b y)) o (\y. y - x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; SMOOTH_BUMP_SMOOTH] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST];
      ALL_TAC] THEN
    EXISTS_TAC `(:real^N) DIFF cball(x,b)` THEN
    REWRITE_TAC[GSYM closed; CLOSED_CBALL; IN_DIFF; IN_UNIV; IN_CBALL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~((y:real^N) IN U)` THEN UNDISCH_TAC `cball(x:real^N,d2) SUBSET U` THEN
      REWRITE_TAC[SUBSET; IN_CBALL] THEN ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC WANL_SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `\y:real^N. vec 0:real^1` THEN
    REWRITE_TAC[SMOOTH_MAP_ON_CONST; GSYM closed; CLOSED_CBALL] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_CBALL; REAL_NOT_LE] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[LIFT_NUM] THEN REWRITE_TAC[GSYM LIFT_NUM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_RING `c = &0 ==> &0 = c * v`) THEN
    MATCH_MP_TAC SMOOTH_BUMP_0 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `b < dist(x:real^N,z)` THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPECL [`x:real^N`; `z:real^N`] NORM_SUB) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `llap (\z:real^N. mat 1) v y` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `ball(x:real^N,a)` THEN
    ASM_SIMP_TAC[OPEN_BALL];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Directional derivatives of smooth functions in coordinates.             *)

let WANL_FD_LINEAR = prove
 (`!(w:real^N->real^K) p.
        smooth_map_on (:real^N) w ==> linear(frechet_derivative w (at p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real^K`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
  DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative]));;

let WANL_FD_EXPAND = prove
 (`!(w:real^N->real) p z.
        smooth_map_on (:real^N) (\y. lift(w y))
        ==> drop(frechet_derivative (\y. lift(w y)) (at p) z) =
            sum(1..dimindex(:N))
               (\i. z$i * drop(frechet_derivative (\y. lift(w y)) (at p) (basis i)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `p:real^N` o MATCH_MP WANL_FD_LINEAR) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; DROP_VSUM; o_DEF] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_CMUL]);;

let WANL_FD_AFFINE_COMPOSE = prove
 (`!(G:real^N->real^1) x s z v.
        smooth_map_on (:real^N) G
        ==> frechet_derivative (\z. G(x - s % z)) (at z) v =
            --s % frechet_derivative G (at (x - s % z)) v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((\z. (G:real^N->real^1)(x - s % z)) has_derivative
     (frechet_derivative G (at (x - s % z)) o (\h. --s % h))) (at z)`
  MP_TAC THENL
   [SUBGOAL_THEN `(\z. (G:real^N->real^1)(x - s % z)) = G o (\z. x - s % z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(\h:real^N. --s % h) = (\h. vec 0 - s % h)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
      MP_TAC(ISPECL [`(:real^N)`; `G:real^N->real^1`] SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
  REWRITE_TAC[o_THM] THEN
  MP_TAC(ISPECL [`G:real^N->real^1`; `x - s % z:real^N`] WANL_FD_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]));;

(* The derivative of the mean is an integral of grad wanl_pot . grad w,      *)
(* which vanishes by integration by parts when w is harmonic.               *)

let WANL_MVP_IBP = prove
 (`!(w:real^N->real) x s d1.
        smooth_map_on (:real^N) (\y. lift(w y)) /\
        (!y. y IN ball(x,d1) ==> llap (\z:real^N. mat 1) w y = &0) /\
        &0 <= s /\ s < d1
        ==> ((\z. lift(wan_mk z *
                       sum(1..dimindex(:N))
                         (\i. z$i * drop(frechet_derivative (\y. lift(w y))
                                           (at (x - s % z)) (basis i)))))
             has_integral vec 0) (:real^N)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `G = \i p. frechet_derivative (\y. lift((w:real^N->real) y)) (at p) (basis i)` THEN
  SUBGOAL_THEN
   `!i p. frechet_derivative (\y. lift((w:real^N->real) y)) (at p) (basis i) =
          (G:num->real^N->real^1) i p`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. smooth_map_on (:real^N) ((G:num->real^N->real^1) i)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "G" THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[OPEN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on (:real^N) (\z. (G:num->real^N->real^1) i (x - s % z))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(\z. (G:num->real^N->real^1) i (x - s % z)) = G i o (\z. x - s % z)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^N)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  (* integration by parts in each coordinate direction *)
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ((\z. lift(drop(frechet_derivative (\y. lift(wanl_pot y)) (at z) (basis i)) *
                       drop((G:num->real^N->real^1) i (x - s % z)) +
                       wanl_pot z *
                       drop(frechet_derivative (\y. lift(drop(G i (x - s % y))))
                              (at z) (basis i))))
             has_integral vec 0) (:real^N)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_TEST_IBP_UNIV THEN
    EXISTS_TAC `cball(vec 0:real^N,&1)` THEN
    REWRITE_TAC[WANL_POT_SMOOTH; COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN
    ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
    MESON_TAC[WANL_POT_ZERO; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `vec 0:real^1 = vsum(1..dimindex(:N)) (\i. vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[VSUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\z. vsum(1..dimindex(:N))
          (\i. lift(drop(frechet_derivative (\y. lift(wanl_pot y)) (at z) (basis i)) *
                    drop((G:num->real^N->real^1) i (x - s % z)) +
                    wanl_pot z *
                    drop(frechet_derivative (\y. lift(drop(G i (x - s % y))))
                           (at z) (basis i))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_UNIV] THEN
  REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  ASM_SIMP_TAC[WANL_FD_AFFINE_COMPOSE; WANL_POT_FD; DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VSUM; o_DEF; LIFT_DROP; SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
       (\i. (wan_mk z * (z dot basis i)) * drop((G:num->real^N->real^1) i (x - s % z))) =
    wan_mk z * sum(1..dimindex(:N)) (\i. z$i * drop(G i (x - s % z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[DOT_BASIS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = &0 ==> a + y = a`) THEN
  REWRITE_TAC[REAL_ARITH `p * --s * q = --(s * p * q)`; SUM_NEG; SUM_LMUL] THEN
  REWRITE_TAC[REAL_NEG_EQ_0; REAL_ENTIRE] THEN DISJ2_TAC THEN
  ASM_CASES_TAC `&1 <= norm(z:real^N)` THENL
   [DISJ1_TAC THEN ASM_SIMP_TAC[WANL_POT_ZERO]; DISJ2_TAC] THEN
  EXPAND_TAC "G" THEN
  MP_TAC(ISPECL [`(:real^N)`; `w:real^N->real`; `x - s % z:real^N`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^N,x - y) = norm y`; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `s * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN MP_TAC(ISPEC `z:real^N` NORM_POS_LE) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The mean M(s) = int wan_mk z w(x - s z) dz is constant for 0 <= s <= d.   *)

let WANL_MVP_CONTINUOUS_TERM = prove
 (`!(w:real^N->real) x.
        smooth_map_on (:real^N) (\y. lift(w y))
        ==> (\p:real^(N,1)finite_sum.
               lift(--(wan_mk(fstcart p) *
                       sum(1..dimindex(:N))
                         (\i. fstcart p$i *
                              drop(frechet_derivative (\y. lift(w y))
                                     (at (x - drop(sndcart p) % fstcart p)) (basis i))))))
            continuous_on (:real^(N,1)finite_sum)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIFT_NEG; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `lift o (\p:real^(N,1)finite_sum. wan_mk(fstcart p)) =
                  (\z. lift(wan_mk z)) o fstcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[WAN_MK_PROPS];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUM; o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL; LIFT_DROP] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\p:real^(N,1)finite_sum.
       frechet_derivative (\y. lift((w:real^N->real) y))
         (at (x - drop(sndcart p) % fstcart p)) (basis i)) =
    (\q. frechet_derivative (\y. lift(w y)) (at q) (basis i)) o
    (\p. x - drop(sndcart p) % fstcart p)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART;
             ETA_AX];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[OPEN_UNIV]]);;

let WANL_CBALL_SUBSET_CUBE = prove
 (`cball(vec 0:real^N,&1) SUBSET interval[--vec 1,vec 1]`,
  REWRITE_TAC[SUBSET; IN_CBALL_0; IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`x:real^N`; `i:num`] COMPONENT_LE_NORM) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let WANL_MVP_MEAN_CONST = prove
 (`!(w:real^N->real) x d d1.
        smooth_map_on (:real^N) (\y. lift(w y)) /\
        (!y. y IN ball(x,d1) ==> llap (\z:real^N. mat 1) w y = &0) /\
        &0 < d /\ d < d1
        ==> integral (:real^N) (\z. lift(wan_mk z * w(x - d % z))) = lift(w x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!g:real^N->real^1. (!z. ~(z IN cball(vec 0,&1)) ==> g z = vec 0)
                       ==> integral (interval[--vec 1,vec 1]) g = integral (:real^N) g`
  (LABEL_TAC "cube") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `cball(vec 0:real^N,&1)` THEN
    ASM_REWRITE_TAC[WANL_CBALL_SUBSET_CUBE; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. ~(z IN cball(vec 0,&1)) ==> wan_mk z = &0` (LABEL_TAC "mk0") THENL
   [REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN MESON_TAC[WAN_MK_PROPS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the derivative of the mean vanishes *)
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,d]
        ==> integral (interval[--vec 1,vec 1])
              (\z. lift(--(wan_mk z *
                           sum(1..dimindex(:N))
                             (\i. z$i * drop(frechet_derivative (\y. lift((w:real^N->real) y))
                                               (at (x - t % z)) (basis i)))))) = vec 0`
  (LABEL_TAC "dz") THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_TAC THEN
    USE_THEN "cube" (fun th -> W(fun (_,w) -> MP_TAC(PART_MATCH (lhand o rand) th (lhand w)))) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
      USE_THEN "mk0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((z:real^N) IN cball(vec 0,&1))`)]) THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_NEG_0; LIFT_NUM];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN REWRITE_TAC[LIFT_NEG] THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_NEG_0] THEN MATCH_MP_TAC HAS_INTEGRAL_NEG THEN
    MATCH_MP_TAC WANL_MVP_IBP THEN EXISTS_TAC `d1:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN real_interval[&0,d]
        ==> ((\s. drop(integral (interval[--vec 1,vec 1])
                        (\z. lift(wan_mk z * (w:real^N->real)(x - s % z)))))
             has_real_derivative &0) (atreal t within real_interval[&0,d])`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\z s. wan_mk z * (w:real^N->real)(x - s % z)`;
      `\z s. --(wan_mk z *
                sum(1..dimindex(:N))
                  (\i. z$i * drop(frechet_derivative (\y. lift((w:real^N->real) y))
                                     (at (x - s % z)) (basis i))))`;
      `--vec 1:real^N`; `vec 1:real^N`; `&0`; `d:real`; `t:real`]
     NSPU_REAL_PARAMETRIC_INTEGRAL) THEN
    ASM_SIMP_TAC[DROP_VEC] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:real^N`; `s:real`] THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN
      MP_TAC(ISPECL [`\y. lift((w:real^N->real) y)`;
                     `frechet_derivative (\y. lift((w:real^N->real) y)) (at (x - s % z))`;
                     `x:real^N`; `--z:real^N`; `s:real`] WANL_LINE_REAL_DERIVATIVE) THEN
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_RNEG; GSYM VECTOR_SUB] THEN
      ANTS_TAC THENL
       [MP_TAC(ISPECL [`(:real^N)`; `\y. lift((w:real^N->real) y)`]
               SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
        ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(ISPECL [`\y. lift((w:real^N->real) y)`; `x - s % z:real^N`] WANL_FD_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]) THEN
      REWRITE_TAC[DROP_NEG] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC WANL_FD_EXPAND THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^(N,1)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN
      MP_TAC(ISPECL [`w:real^N->real`; `x:real^N`] WANL_MVP_CONTINUOUS_TERM) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN REWRITE_TAC[WAN_MK_PROPS];
        SUBGOAL_THEN `(\z. lift((w:real^N->real)(x - s % z))) =
                      (\y. lift(w y)) o (\z. x - s % z)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_CMUL;
                   CONTINUOUS_ON_ID];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
          ASM_SIMP_TAC[SUBSET_UNIV; SMOOTH_MAP_ON_CONTINUOUS_ON]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s. drop(integral (interval[--vec 1,vec 1])
                (\z. lift(wan_mk z * (w:real^N->real)(x - s % z))))`;
    `real_interval[&0,d]`] HAS_REAL_DERIVATIVE_ZERO_CONSTANT) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (LABEL_TAC "const" o BETA_RULE)) THEN
  SUBGOAL_THEN
   `drop(integral (interval[--vec 1,vec 1])
           (\z. lift(wan_mk z * (w:real^N->real)(x - d % z)))) =
    drop(integral (interval[--vec 1,vec 1]) (\z. lift(wan_mk z * w(x - &0 % z))))`
  MP_TAC THENL
   [USE_THEN "const" (MP_TAC o SPEC `&0`) THEN USE_THEN "const" (MP_TAC o SPEC `d:real`) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN
   `!v:real^N->real. integral (interval[--vec 1,vec 1]) (\z. lift(wan_mk z * v z)) =
                     integral (:real^N) (\z. lift(wan_mk z * v z))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN USE_THEN "cube" MATCH_MP_TAC THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "mk0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((z:real^N) IN cball(vec 0,&1))`)]) THEN
    REWRITE_TAC[REAL_MUL_LZERO; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN `integral (:real^N) (\z. lift(wan_mk z * (w:real^N->real) x)) = lift(w x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    SUBGOAL_THEN `(\z:real^N. lift(wan_mk z * (w:real^N->real) x)) =
                  (\z. w x % lift(wan_mk z))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL] THEN GEN_TAC THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
    REWRITE_TAC[WAN_MK_PROPS];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_DROP; DROP_EQ]);;

(* Rescaling the mollifier to the unit kernel.                               *)

let WANL_AFFINE_IMAGE_UNIV = prove
 (`!m (c:real^N). ~(m = &0) ==> IMAGE (\y. inv m % y + --(inv m % c)) (:real^N) = (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
  X_GEN_TAC `z:real^N` THEN EXISTS_TAC `m % z + c:real^N` THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  VECTOR_ARITH_TAC);;

let WANL_MOLL_RESCALE = prove
 (`!d (u:real^N->real^K) x.
        &0 < d /\ u continuous_on (:real^N)
        ==> wan_moll d u x = integral (:real^N) (\z. wan_mk z % u(x - d % z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. wan_mk z % (u:real^N->real^K)(x - d % z)) integrable_on (:real^N)`
  MP_TAC THENL
   [MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN
    EXISTS_TAC `cball(vec 0:real^N,&1)` THEN
    REWRITE_TAC[OPEN_UNIV; COMPACT_CBALL; SUBSET_UNIV; IN_UNIV; IN_CBALL_0; REAL_NOT_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
        REWRITE_TAC[WAN_MK_PROPS];
        SUBGOAL_THEN `(\z. (u:real^N->real^K)(x - d % z)) = u o (\z. x - d % z)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_CMUL;
                 CONTINUOUS_ON_ID] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      MESON_TAC[WAN_MK_PROPS; REAL_LT_IMP_LE; VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `i:real^K`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[WAN_MOLL_EQ] THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `~(--inv d = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NEG_EQ_0; REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--inv d`; `inv d % x:real^N`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
  ASM_SIMP_TAC[WANL_AFFINE_IMAGE_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(d) pow dimindex(:N)` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  MATCH_MP_TAC(MESON[] `(f:real^N->real^K) = g /\ (a:real^K) = b
                        ==> (f has_integral a) (s:real^N->bool) ==> (g has_integral b) s`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; wan_mke] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `x - d % (--a % y + a % x):real^N = x + (d * a) % y - (d * a) % x`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_ABS_NEG; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`; REAL_POW_INV; REAL_INV_INV] THEN
    SUBGOAL_THEN `~(d pow dimindex(:N) = &0)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_NZ THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]]);;

(* The radial mean value property.                                           *)

let WANL_MOLL_MVP = prove
 (`!(U:real^N->bool) (v:real^N->real) x d.
        open U /\ smooth_map_on U (\y. lift(v y)) /\
        (!y. y IN U ==> llap (\z:real^N. mat 1) v y = &0) /\
        &0 < d /\ cball(x,d) SUBSET U
        ==> wan_moll d (\y. lift(v y)) x = lift(v x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `v:real^N->real`; `x:real^N`; `d:real`]
         WANL_HARMONIC_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real` (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `wan_moll d (\y. lift((v:real^N->real) y)) x = wan_moll d (\y. lift(w y)) x`
  SUBST1_TAC THENL
   [REWRITE_TAC[WAN_MOLL_EQ] THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `d <= norm(x - y:real^N)` THENL
     [ASM_SIMP_TAC[WAN_MKE_ZERO; VECTOR_MUL_LZERO]; ALL_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && not(can (find_term (fun u -> u = `llap`)) (concl th)) &&
      can (find_term (fun u -> u = `ball(x:real^N,d1)`)) (concl th))) THEN
    REWRITE_TAC[IN_BALL; dist] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->real) x = w x` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term (fun u -> u = `(w:real^N->real) y`)) (concl th) &&
      not(can (find_term (fun u -> u = `mat 1:real^N^N`)) (concl th)))) THEN
    REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real`; `\y. lift((w:real^N->real) y)`; `x:real^N`] WANL_MOLL_RESCALE) THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM LIFT_CMUL] THEN MATCH_MP_TAC WANL_MVP_MEAN_CONST THEN
  EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Laplacians of convolutions, and the harmonicity of the                    *)
(* mollification of a weakly harmonic function.                              *)
(* ========================================================================= *)

let WANL_LLAP_DPART = prove
 (`!(phi:real^N->real) y.
        smooth_map_on (:real^N) (\x. lift(phi x))
        ==> llap (\z:real^N. mat 1) phi y =
            sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i phi) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `phi:real^N->real`; `y:real^N`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[wan_dpart; LIFT_DROP]);;

let WANL_DPART_NEG = prove
 (`!(f:real^N->real) i y.
        (\x. lift(f x)) differentiable (at y)
        ==> wan_dpart i (\x. --(f x)) y = --(wan_dpart i f y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dpart; LIFT_NEG] THEN
  SUBGOAL_THEN
   `frechet_derivative (\x. --lift((f:real^N->real) x)) (at y) =
    (\h. --(frechet_derivative (\x. lift(f x)) (at y) h))`
  (fun th -> REWRITE_TAC[th; DROP_NEG]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN
  ASM_REWRITE_TAC[ETA_AX; GSYM FRECHET_DERIVATIVE_WORKS]);;

let WANL_LLAP_REFLECT = prove
 (`!(k:real^N->real) x y.
        wan_test (:real^N) k
        ==> llap (\z:real^N. mat 1) (\y. k(x - y)) y =
            sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i k) (x - y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o SPEC `x:real^N` o MATCH_MP WAN_TEST_UNIV_REFLECT) THEN
  MP_TAC(ISPECL [`\y:real^N. (k:real^N->real)(x - y)`; `y:real^N`] WANL_LLAP_DPART) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `wan_test (:real^N) (\y. (k:real^N->real)(x - y))` THEN SIMP_TAC[wan_test];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `wan_dpart i (\y. (k:real^N->real)(x - y)) =
                (\y. --(wan_dpart i k (x - y)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[WAN_REFLECT_DPART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->real`; `i:num`] WAN_TEST_DPART_TEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\y:real^N. wan_dpart i (k:real^N->real) (x - y)`; `i:num`;
                            `y:real^N`] WANL_DPART_NEG)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MP_TAC(ISPECL [`wan_dpart i (k:real^N->real)`; `x:real^N`] WAN_TEST_UNIV_REFLECT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[wan_test];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[WAN_REFLECT_DPART; REAL_NEG_NEG]);;

(* The Laplacian of a convolution with a test kernel.                        *)

let WANL_KCONV_DPART2 = prove
 (`!(k:real^N->real) (U:real^N->real^1) i x.
        wan_test (:real^N) k /\ wan_lloc (:real^N) U
        ==> frechet_derivative
              (\z. frechet_derivative (\w. lift(drop(wan_kconv k U w))) (at z) (basis i))
              (at x) (basis i) =
            wan_kconv (wan_dpart i (wan_dpart i k)) U x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  SUBGOAL_THEN
   `(\z. frechet_derivative (wan_kconv (k:real^N->real) (U:real^N->real^1)) (at z) (basis i)) =
    wan_kconv (wan_dpart i k) U`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
    MP_TAC(ISPECL [`k:real^N->real`; `U:real^N->real^1`; `i:num`; `z:real^N`]
           WAN_KCONV_PARTIAL) THEN
    ASM_REWRITE_TAC[partial_derivative];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_dpart i (k:real^N->real)`; `U:real^N->real^1`; `i:num`; `x:real^N`]
         WAN_KCONV_PARTIAL) THEN
  ASM_SIMP_TAC[WAN_TEST_DPART_TEST; partial_derivative]);;

let WANL_KCONV_LLAP = prove
 (`!(k:real^N->real) (U:real^N->real^1) x.
        wan_test (:real^N) k /\ wan_lloc (:real^N) U
        ==> llap (\y:real^N. mat 1) (\z. drop(wan_kconv k U z)) x =
            drop(integral (:real^N)
                   (\y. sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i k) (x - y)) % U y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `\z. drop(wan_kconv (k:real^N->real) (U:real^N->real^1) z)`;
                 `x:real^N`] LLAP_FLAT) THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; LIFT_DROP; ETA_AX; WAN_KCONV_SMOOTH] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:real^N->real`; `U:real^N->real^1`] WANL_KCONV_DPART2) THEN
  ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VSUM_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_VSUM o rand o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN
    ASM_SIMP_TAC[WAN_TEST_DPART_TEST];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; wan_kconv]);;

(* The Laplacian of the mollifier kernel vanishes off cball(0,e).            *)

let WANL_MKE_LAP_ZERO = prove
 (`!e (z:real^N).
        &0 < e /\ ~(z IN cball(vec 0,e))
        ==> sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i (wan_mke e)) z) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `cball(vec 0:real^N,e)` THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`wan_mke e:real^N->real`; `i:num`] WAN_TEST_DPART_TEST) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST; wan_test];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN EXISTS_TAC `cball(vec 0:real^N,e)` THEN
    ASM_REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
     [MP_TAC(INST_TYPE [`:N`,`:M`] (ISPEC `e:real` WAN_MKE_TEST)) THEN ASM_SIMP_TAC[wan_test];
      REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN
      MESON_TAC[WAN_MKE_ZERO; REAL_LT_IMP_LE; ASSUME `&0 < e`]]]);;

(* Mollifications of weakly harmonic functions are harmonic.                  *)

let WANL_WEAK_HARM_MOLL = prove
 (`!(s:real^N->bool) (u:real^N->real) (U:real^N->real^1) e x.
        open s /\
        (!phi. wan_test s phi
               ==> integral s (\x. lift(u x * llap (\y:real^N. mat 1) phi x)) = vec 0) /\
        wan_lloc (:real^N) U /\ &0 < e /\ cball(x,e) SUBSET s /\
        (!y. y IN cball(x,e) ==> U y = lift(u y))
        ==> llap (\y:real^N. mat 1) (\z. drop(wan_moll e U z)) x = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_moll] THEN
  MP_TAC(ISPECL [`wan_mke e:real^N->real`; `U:real^N->real^1`; `x:real^N`] WANL_KCONV_LLAP) THEN
  ASM_SIMP_TAC[WAN_MKE_TEST] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `L = \z:real^N. sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i (wan_mke e)) z)` THEN
  SUBGOAL_THEN `!y:real^N. ~(y IN cball(x,e)) ==> L(x - y) = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "L" THEN MATCH_MP_TAC WANL_MKE_LAP_ZERO THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN
    UNDISCH_TAC `~((y:real^N) IN cball(x,e))` THEN REWRITE_TAC[IN_CBALL; dist];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. sum(1..dimindex(:N)) (\i. wan_dpart i (wan_dpart i (wan_mke e)) (x - y)) =
               L(x - y)`
  (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* the weak equation for the test function y |-> mke(x - y) *)
  FIRST_X_ASSUM(MP_TAC o SPEC `\y:real^N. wan_mke e (x - y)` o check (fun th ->
    is_forall(concl th) && can (find_term (fun u -> u = `wan_test (s:real^N->bool)`)) (concl th))) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`wan_mke e:real^N->real`; `x:real^N`] WAN_TEST_UNIV_REFLECT) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST; wan_test] THEN STRIP_TAC THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    REWRITE_TAC[IN_CBALL; dist; REAL_NOT_LE] THEN
    MESON_TAC[WAN_MKE_ZERO; REAL_LT_IMP_LE; ASSUME `&0 < e`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`wan_mke e:real^N->real`; `x:real^N`] WANL_LLAP_REFLECT) THEN
  ASM_SIMP_TAC[WAN_MKE_TEST] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `integral s (\y:real^N. lift(u y * L(x - y))) =
    integral (cball(x,e)) (\y. lift(u y * L(x - y)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN ASM_SIMP_TAC[SUBSET_REFL; REAL_MUL_RZERO; LIFT_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (:real^N) (\y. L(x - y) % (U:real^N->real^1) y) =
    integral (cball(x,e)) (\y. L(x - y) % U y)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
    EXISTS_TAC `cball(x:real^N,e)` THEN
    ASM_SIMP_TAC[SUBSET_REFL; SUBSET_UNIV; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (cball(x,e)) (\y. L(x - y) % (U:real^N->real^1) y) =
    integral (cball(x,e)) (\y:real^N. lift(u y * L(x - y)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DROP_VEC]]);;

(* Linearity and an L^2 bound for mollifications at a point.                 *)

let WANL_MOLL_SUB_FN = prove
 (`!e (u:real^N->real^K) v x.
        &0 < e /\ wan_lloc (:real^N) u /\ wan_lloc (:real^N) v
        ==> wan_moll e (\y. u y - v y) x = wan_moll e u x - wan_moll e v x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WAN_MOLL_EQ; VECTOR_SUB_LDISTRIB] THEN
  MATCH_MP_TAC INTEGRAL_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC WAN_KCONV_INTEGRABLE THEN ASM_SIMP_TAC[WAN_MKE_TEST]);;

let WANL_MOLL_L2_BOUND = prove
 (`?B. &0 < B /\
       !e (f:real^N->real^1) x.
          &0 < e /\ f IN lspace (:real^N) (&2)
          ==> norm(wan_moll e f x) pow 2 <=
              (B * inv(e) pow dimindex(:N)) *
              drop(integral (:real^N) (\y. lift(norm(f y) pow 2)))`,
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:M`] WAN_MKE_BOUND) THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WAN_L2_LLOC) THEN
  ABBREV_TAC `g = \y:real^N. drop((f:real^N->real^1) y)` THEN
  SUBGOAL_THEN `!y:real^N. (f:real^N->real^1) y = lift(g y)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. norm((f:real^N->real^1) y) pow 2 = g y pow 2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_LIFT; REAL_POW2_ABS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[WAN_MOLL_EQ; NORM_1] THEN
  REWRITE_TAC[REAL_POW2_ABS; GSYM LIFT_CMUL] THEN
  ABBREV_TAC `w = \y:real^N. wan_mke e (x - y)` THEN
  SUBGOAL_THEN `!y:real^N. wan_mke e (x - y) = w y`
  (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. &0 <= w y /\ w y <= B * inv e pow dimindex(:N)`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[WAN_MKE_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `((\y:real^N. lift(w y)) has_integral lift(&1)) (:real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN ASM_SIMP_TAC[WAN_MKE_INTEGRAL_AT]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^N. lift(w y * g y)) integrable_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`wan_mke e:real^N->real`; `f:real^N->real^1`; `x:real^N`]
           WAN_KCONV_INTEGRABLE) THEN
    ASM_SIMP_TAC[WAN_MKE_TEST; LIFT_CMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^N. lift(g y pow 2)) absolutely_integrable_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_NONNEG_ABS_INTEGRABLE THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REWRITE_TAC[GSYM(ASSUME `!y:real^N. norm((f:real^N->real^1) y) pow 2 = g y pow 2`)] THEN
    MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^N. lift(w y * g y pow 2)) integrable_on (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MP_TAC(ISPECL [`\a:real^1 b:real^1. drop a % b`; `\y:real^N. lift(w y)`;
                   `\y:real^N. lift(g y pow 2)`; `(:real^N)`]
           ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT) THEN
    REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP; GSYM LIFT_CMUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN ASM_MESON_TAC[integrable_on];
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV; NORM_LIFT] THEN
      EXISTS_TAC `B * inv e pow dimindex(:N)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_INV_EQ];
        GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x':real^N` o check (fun th ->
          can (find_term (fun u -> u = `B:real`)) (concl th) && is_forall(concl th))) THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N->real`; `g:real^N->real`] WAN_WEIGHTED_CS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
  SUBGOAL_THEN `drop(integral (:real^N) (\y. lift(w y))) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC(MESON[LIFT_DROP] `(x:real^1) = lift a ==> drop x = a`) THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= &1 * b ==> a <= c`) THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN
  ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[DROP_CMUL; LIFT_DROP; IN_UNIV] THEN GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

(* ========================================================================= *)
(* Weyl's lemma.  Locally, with U = chi u (chi a cutoff equal                *)
(* to 1 near the ball), the mollifications u_e = wan_moll e U are harmonic,  *)
(* so u_e = wan_moll (r/2) u_e near the centre; letting e -> 0 (a.e. and in  *)
(* L^2) gives U = wan_moll (r/2) U a.e.  Gluing by WAN_LOCAL_SMOOTH_AE.      *)
(* ========================================================================= *)

let WANL_WEYL_LOCAL = prove
 (`!(s:real^N->bool) (u:real^N->real) c r.
        open s /\ wan_l2loc s (\x. lift(u x)) /\
        (!phi. wan_test s phi
               ==> integral s (\x. lift(u x * llap (\y:real^N. mat 1) phi x)) = vec 0) /\
        &0 < r /\ cball(c,&4 * r) SUBSET s
        ==> ?W. smooth_map_on (:real^N) W /\
                (!x. x IN ball(c,r) ==> llap (\y:real^N. mat 1) (\z. drop(W z)) x = &0) /\
                negligible {x | x IN ball(c,r / &2) /\ ~(lift(u x) = W x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `chi = \y:real^N. smooth_bump ((&4 * r) * (&1 - inv(&0 + &2))) (&4 * r) (y - c)` THEN
  SUBGOAL_THEN `wan_test s (chi:real^N->real)` ASSUME_TAC THENL
   [EXPAND_TAC "chi" THEN MATCH_MP_TAC WAN_BALL_BUMP_TEST THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN cball(c,&2 * r) ==> chi y = &1` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
    EXPAND_TAC "chi" THEN MATCH_MP_TAC SMOOTH_BUMP_1 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(ISPECL [`c:real^N`; `y:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. ~(y IN cball(c,&4 * r)) ==> chi y = &0` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_CBALL; dist; REAL_NOT_LE] THEN DISCH_TAC THEN
    EXPAND_TAC "chi" THEN MATCH_MP_TAC SMOOTH_BUMP_0 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC(ISPECL [`c:real^N`; `y:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `U = \y:real^N. (chi:real^N->real) y % lift(u y)` THEN
  SUBGOAL_THEN `(U:real^N->real^1) IN lspace (:real^N) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC WAN_L2LOC_CUTOFF THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP WAN_L2_LLOC) THEN
  SUBGOAL_THEN `!y:real^N. y IN cball(c,&2 * r) ==> U y = lift(u y)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "U" THEN ASM_SIMP_TAC[VECTOR_MUL_LID]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. ~(y IN cball(c,&4 * r)) ==> (U:real^N->real^1) y = vec 0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "U" THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  (* mollifications with radius below r are harmonic on ball(c,r) *)
  SUBGOAL_THEN
   `!e x. &0 < e /\ e < r /\ x IN ball(c:real^N,r)
          ==> llap (\y:real^N. mat 1) (\z. drop(wan_moll e (U:real^N->real^1) z)) x = &0`
  (LABEL_TAC "harm") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WANL_WEAK_HARM_MOLL THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->real`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cball(x:real^N,e) SUBSET cball(c,&2 * r)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN ball(c,r)` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN DISCH_TAC THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:real^N`; `x:real^N`; `y:real^N`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(c:real^N,&4 * r)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(c:real^N,&2 * r)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `wan_moll (r / &2) (U:real^N->real^1)` THEN
  ASM_SIMP_TAC[WAN_MOLL_SMOOTH; REAL_HALF] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "harm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the mean value property for the u_e near the centre *)
  SUBGOAL_THEN
   `!e x. &0 < e /\ e < r /\ x IN ball(c:real^N,r / &2)
          ==> wan_moll (r / &2) (wan_moll e (U:real^N->real^1)) x = wan_moll e U x`
  (LABEL_TAC "mvp") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ball(c:real^N,r)`; `\z. drop(wan_moll e (U:real^N->real^1) z)`;
                   `x:real^N`; `r / &2`] WANL_MOLL_MVP) THEN
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_SIMP_TAC[SUBSET_UNIV; WAN_MOLL_SMOOTH];
      REPEAT STRIP_TAC THEN USE_THEN "harm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^N) IN ball(c,r / &2)` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN DISCH_TAC THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:real^N`; `x:real^N`; `y:real^N`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a.e. and L^2 convergence of u_e *)
  MP_TAC(ISPEC `U:real^N->real^1` WAN_MOLL_AE_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(U:real^N->real^1) x = lift(u x)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun u -> u = `lift((u:real^N->real) y)`)) (concl th) && is_forall(concl th))) THEN
    UNDISCH_TAC `(x:real^N) IN ball(c,r / &2)` THEN REWRITE_TAC[IN_BALL; IN_CBALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `delta = norm(wan_moll (r / &2) (U:real^N->real^1) x - U x)` THEN
  SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `delta / &2`]) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WANL_MOLL_L2_BOUND) THEN
  ABBREV_TAC `C = B * inv(r / &2) pow dimindex(:N)` THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->real^1`; `cball(c:real^N,&4 * r)`] WAN_MOLL_L2_CONV) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(delta / &2) pow 2 / C`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (min d0 d1) r / &2` THEN
  SUBGOAL_THEN `&0 < e /\ e < d0 /\ e < d1 /\ e < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
    can (find_term (fun u -> u = `d1:real`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real` o check (fun th ->
    can (find_term (fun u -> u = `d0:real`)) (concl th) && is_forall(concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the bound on wan_moll (r/2) (u_e - U) at x *)
  SUBGOAL_THEN
   `norm(wan_moll (r / &2) (\y. wan_moll e (U:real^N->real^1) y - U y) x) < delta / &2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `C * drop(integral (:real^N)
                       (\y. lift(norm(wan_moll e (U:real^N->real^1) y - U y) pow 2)))` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "C" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun u -> u = `B:real`)) (concl th) && is_forall(concl th))) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[ETA_AX] THEN
      ASM_SIMP_TAC[WAN_MOLL_L2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC
     `drop(integral (:real^N) (\x. lift(norm(wan_moll e (U:real^N->real^1) x - U x) pow 2))) <
      (delta / &2) pow 2 / C` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r / &2`; `wan_moll e (U:real^N->real^1)`; `U:real^N->real^1`; `x:real^N`]
         WANL_MOLL_SUB_FN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC WAN_L2_LLOC THEN ASM_SIMP_TAC[WAN_MOLL_L2];
    DISCH_THEN SUBST_ALL_TAC] THEN
  USE_THEN "mvp" (MP_TAC o SPECL [`e:real`; `x:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
  MP_TAC(ASSUME `norm(wan_moll e (U:real^N->real^1) x - lift(u x)) < delta / &2`) THEN
  MP_TAC(ASSUME `norm(wan_moll e (U:real^N->real^1) x - wan_moll (r / &2) U x) < delta / &2`) THEN
  MP_TAC(ASSUME `norm(wan_moll (r / &2) (U:real^N->real^1) x - U x) = delta`) THEN
  REWRITE_TAC[ASSUME `(U:real^N->real^1) x = lift(u x)`] THEN
  CONV_TAC NORM_ARITH);;

let WAN_WEYL = prove
 (`!n:N->bool. WAN_WEYL_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[WAN_WEYL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `u:real^N->real`] THEN STRIP_TAC THEN
  (* radii and local smooth harmonic representatives *)
  SUBGOAL_THEN
   `!x. x IN s ==> ?r W. &0 < r /\ cball(x:real^N,&4 * r) SUBSET s /\
                         smooth_map_on (:real^N) W /\
                         (!y. y IN ball(x,r)
                              ==> llap (\z:real^N. mat 1) (\z. drop(W z)) y = &0) /\
                         negligible {y | y IN ball(x,r / &2) /\ ~(lift(u y) = W y)}`
  (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e / &4` THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->real`; `x:real^N`; `e / &4`]
           WANL_WEYL_LOCAL) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&4 * e / &4 = e`] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:real^N->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W:real^N->real^1` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real` (X_CHOOSE_THEN `W:real^N->real^N->real^1`
    (LABEL_TAC "loc"))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(u x)`] WAN_LOCAL_SMOOTH_AE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN s`)) THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ball(x:real^N,r x / &2)`; `(W:real^N->real^N->real^1) x`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^N,&4 * r x)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN X_GEN_TAC `y:real^N` THEN
      UNDISCH_TAC `&0 < (r:real^N->real) x` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real^1`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o BETA_RULE))) THEN
  EXISTS_TAC `\x:real^N. drop(w x)` THEN ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{z | z IN s /\ ~(lift((u:real^N->real) z) = w z)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_MESON_TAC[]] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN s`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `ball(x:real^N,r x / &2) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^N,&4 * r x)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN X_GEN_TAC `y:real^N` THEN
    UNDISCH_TAC `&0 < (r:real^N->real) x` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(x:real^N,r x / &2) ==> (w:real^N->real^1) y = W x y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_CONT_AE_EQ_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; SUBSET_UNIV];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{z | z IN s /\ ~(lift((u:real^N->real) z) = w z)} UNION
                  {y | y IN ball(x,r x / &2) /\ ~(lift(u y) = (W:real^N->real^N->real^1) x y)}` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `llap (\z:real^N. mat 1) (\z. drop((W:real^N->real^N->real^1) x z)) x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LLAP_LOCAL THEN EXISTS_TAC `ball(x:real^N,r x / &2)` THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_HALF];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CENTRE_IN_BALL]]);;

(* ========================================================================= *)
(* Interior derivative estimates for harmonic functions and                  *)
(* WAN_HARM_GRAD_OSC.                                                        *)
(* ========================================================================= *)

let WANL_INTEGRAL_CS = prove
 (`!(f:real^N->real) g s.
        (\x. lift(f x pow 2)) integrable_on s /\ (\x. lift(g x pow 2)) integrable_on s /\
        (\x. lift(f x * g x)) integrable_on s
        ==> drop(integral s (\x. lift(f x * g x))) pow 2 <=
            drop(integral s (\x. lift(f x pow 2))) * drop(integral s (\x. lift(g x pow 2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_QUAD_DISCRIMINANT THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN
  SUBGOAL_THEN
   `drop(integral s (\x:real^N. lift(f x pow 2))) * t pow 2 -
    &2 * drop(integral s (\x. lift(f x * g x))) * t +
    drop(integral s (\x. lift(g x pow 2))) =
    drop(integral s (\x. lift((t * f x - g x) pow 2)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(\x:real^N. lift((t * f x - g x) pow 2)) =
      (\x. (t pow 2 % lift(f x pow 2) - (&2 * t) % lift(f x * g x)) + lift(g x pow 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_SUB; GSYM LIFT_ADD] THEN
      GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRAL_SUB; INTEGRAL_CMUL; INTEGRABLE_CMUL;
                 INTEGRABLE_SUB; DROP_ADD; DROP_SUB; DROP_CMUL] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    SUBGOAL_THEN
     `(\x:real^N. lift((t * f x - g x) pow 2)) =
      (\x. (t pow 2 % lift(f x pow 2) - (&2 * t) % lift(f x * g x)) + lift(g x pow 2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_SUB; GSYM LIFT_ADD] THEN
      GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRABLE_ADD; INTEGRABLE_SUB; INTEGRABLE_CMUL]]]);;

(* The L^2 norm of a derivative of the rescaled kernel.                      *)

let WANL_DPART_MKE_L2 = prove
 (`!i. ?K. &0 <= K /\
           !d (y:real^N). &0 < d
               ==> ((\z. lift(wan_dpart i (wan_mke d) (y - z) pow 2)) has_integral
                    lift(K * inv(d) pow (dimindex(:N) + 2))) (:real^N)`,
  GEN_TAC THEN
  SUBGOAL_THEN `wan_test (:real^N) (wan_dpart i wan_mk)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_TEST_DPART_TEST THEN
    REWRITE_TAC[wan_test; WAN_MK_PROPS; SUBSET_UNIV] THEN
    EXISTS_TAC `cball(vec 0:real^N,&1)` THEN
    REWRITE_TAC[COMPACT_CBALL; IN_CBALL_0; REAL_NOT_LE] THEN
    MESON_TAC[WAN_MK_PROPS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^N. lift(wan_dpart i wan_mk z pow 2)) integrable_on (:real^N)`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [wan_test]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC WAN_NT_INTEGRABLE_COMPACT_SUPPORT THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; IN_UNIV; REAL_POW_ZERO; ARITH_EQ; LIFT_NUM] THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[o_DEF] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[integrable_on] THEN DISCH_THEN(X_CHOOSE_TAC `I0:real^1`) THEN
  EXISTS_TAC `drop I0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`\z:real^N. lift(wan_dpart i wan_mk z pow 2)`; `(:real^N)`]
                 HAS_INTEGRAL_DROP_POS) THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(--inv d = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NEG_EQ_0; REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--inv d`; `inv d % y:real^N`] o
    MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY)) THEN
  ASM_SIMP_TAC[WANL_AFFINE_IMAGE_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `(inv(d) pow (dimindex(:N) + 1)) pow 2` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  MATCH_MP_TAC(MESON[] `(f:real^N->real^1) = g /\ (a:real^1) = b
                        ==> (f has_integral a) (s:real^N->bool) ==> (g has_integral b) s`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^N` THEN
    ASM_SIMP_TAC[WAN_MKE_DPART] THEN REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_POW_MUL] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; REAL_ABS_NEG; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < d ==> abs d = d`] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
  SUBGOAL_THEN `~(inv d pow dimindex(:N) = &0) /\ ~(inv d = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; REAL_INV_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`inv d pow dimindex(:N)`,`q:real`) THEN SPEC_TAC(`inv d`,`x:real`) THEN
  CONV_TAC REAL_FIELD);;

(* Facts about the derivative kernels of the mollifier.                      *)

let WANL_DPART_MKE_FACTS = prove
 (`!d i (y:real^N).
        &0 < d
        ==> (!z. ~(z IN cball(y,d)) ==> wan_dpart i (wan_mke d) (y - z) = &0) /\
            ((\z. lift(wan_dpart i (wan_mke d) (y - z))) has_integral vec 0) (:real^N) /\
            (\z. lift(wan_dpart i (wan_mke d) (y - z))) continuous_on (:real^N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (INST_TYPE [`:N`,`:M`] WAN_MKE_TEST)) THEN
  SUBGOAL_THEN `!z:real^N. ~(z IN cball(vec 0,d)) ==> wan_mke d z = &0` ASSUME_TAC THENL
   [REWRITE_TAC[IN_CBALL_0; REAL_NOT_LE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WAN_MKE_ZERO THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (:real^N) (\x. lift(wan_mke d x))` ASSUME_TAC THENL
   [MP_TAC(INST_TYPE [`:N`,`:M`] (ISPEC `d:real` WAN_MKE_PROPS)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC WAN_TEST_DPART_ZERO THEN
    EXISTS_TAC `cball(vec 0:real^N,d)` THEN ASM_REWRITE_TAC[COMPACT_CBALL] THEN
    UNDISCH_TAC `~((z:real^N) IN cball(y,d))` THEN
    REWRITE_TAC[IN_CBALL; IN_CBALL_0; dist];
    MP_TAC(ISPECL [`\w:real^N. lift(wan_dpart i (wan_mke d) w)`; `vec 0:real^1`; `y:real^N`]
           WAN_KERNEL_SHIFT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lift(wan_mke d x)`; `cball(vec 0:real^N,d)`; `basis i:real^N`]
           WAN_INTEGRAL_DIRDERIV_ZERO) THEN
    ASM_SIMP_TAC[COMPACT_CBALL; LIFT_NUM; wan_dpart; LIFT_DROP; ETA_AX];
    SUBGOAL_THEN `(\z:real^N. lift(wan_dpart i (wan_mke d) (y - z))) =
                  (\x. lift(wan_dpart i (wan_mke d) x)) o (\z. y - z)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MP_TAC(ISPECL [`wan_mke d:real^N->real`; `i:num`] WAN_TEST_DPART_TEST) THEN
    ASM_SIMP_TAC[wan_test]]);;

(* The interior derivative estimate for harmonic functions.                  *)

let WANL_HARMONIC_DPART_BOUND = prove
 (`!i. ?K. &0 <= K /\
           !(U:real^N->bool) (v:real^N->real) y d c.
              open U /\ smooth_map_on U (\x. lift(v x)) /\
              (!x. x IN U ==> llap (\z:real^N. mat 1) v x = &0) /\
              &0 < d /\ cball(y,&2 * d) SUBSET U
              ==> wan_dpart i v y pow 2 <=
                  K * inv(d) pow (dimindex(:N) + 2) *
                  drop(integral (ball(y,&2 * d)) (\z. lift((v z - c) pow 2)))`,
  GEN_TAC THEN
  X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC (SPEC `i:num` (INST_TYPE [`:N`,`:N`] WANL_DPART_MKE_L2)) THEN
  EXISTS_TAC `K:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `v:real^N->real`; `y:real^N`; `&2 * d`]
         WANL_HARMONIC_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real` (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `k = \z:real^N. wan_dpart i (wan_mke d) (y - z)` THEN
  MP_TAC(ISPECL [`d:real`; `i:num`; `y:real^N`] WANL_DPART_MKE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the derivative of v at y as an integral of k (w - c) *)
  SUBGOAL_THEN
   `wan_dpart i v y =
    drop(integral (ball(y,&2 * d)) (\z. lift((k:real^N->real) z * (v z - c))))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `wan_dpart i (w:real^N->real) y` THEN CONJ_TAC THENL
     [REWRITE_TAC[wan_dpart] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
      MATCH_MP_TAC WANL_FD_LOCAL_OPEN THEN EXISTS_TAC `ball(y:real^N,d1)` THEN
      ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `drop(partial_derivative i (wan_moll d (\y. lift((w:real^N->real) y))) y)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[wan_dpart; partial_derivative] THEN AP_TERM_TAC THEN AP_THM_TAC THEN
      MATCH_MP_TAC WANL_FD_LOCAL_OPEN THEN EXISTS_TAC `ball(y:real^N,d)` THEN
      ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC WANL_MOLL_MVP THEN
      EXISTS_TAC `ball(y:real^N,d1)` THEN ASM_SIMP_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        UNDISCH_TAC `(z:real^N) IN ball(y,d)` THEN
        REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN DISCH_TAC THEN
        X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`y:real^N`; `z:real^N`; `q:real^N`] DIST_TRIANGLE) THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:real`; `\y. lift((w:real^N->real) y)`; `i:num`; `y:real^N`]
           WAN_MOLL_PARTIAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[wan_kconv] THEN
    SUBGOAL_THEN
     `integral (:real^N) (\z. wan_dpart i (wan_mke d) (y - z) % lift((w:real^N->real) z)) =
      integral (:real^N) (\z. lift((k:real^N->real) z * (w z - c)))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `(\z:real^N. lift((k:real^N->real) z * (w z - c))) =
        (\z. wan_dpart i (wan_mke d) (y - z) % lift(w z) - c % lift(k z))`
      SUBST1_TAC THENL
       [EXPAND_TAC "k" THEN REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; GSYM LIFT_SUB] THEN
        GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(BETA_RULE(ISPECL [`\z. wan_dpart i (wan_mke d) (y - z) % lift((w:real^N->real) z)`;
                     `\z. c % lift((k:real^N->real) z)`; `(:real^N)`] INTEGRAL_SUB)) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          MP_TAC(ISPECL [`wan_dpart i (wan_mke d):real^N->real`;
                         `\z. lift((w:real^N->real) z)`; `y:real^N`] WAN_KCONV_INTEGRABLE) THEN
          REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_SIMP_TAC[WAN_TEST_DPART_TEST; WAN_MKE_TEST] THEN
          MATCH_MP_TAC WAN_CONTINUOUS_LLOC THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
          MATCH_MP_TAC INTEGRABLE_CMUL THEN EXPAND_TAC "k" THEN
          ASM_MESON_TAC[integrable_on]];
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `integral (:real^N) (\z. c % lift((k:real^N->real) z)) = vec 0`
      SUBST1_TAC THENL
       [MATCH_MP_TAC INTEGRAL_UNIQUE THEN
        GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM(ISPEC `c:real` (GEN_ALL VECTOR_MUL_RZERO))] THEN
        MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN EXPAND_TAC "k" THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[VECTOR_SUB_RZERO]];
      ALL_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral (ball(y,&2 * d)) (\z. lift((k:real^N->real) z * (w z - c)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_EQ THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term (fun u -> u = `d1:real`)) (concl th) &&
        not(can (find_term (fun u -> u = `mat 1:real^N^N`)) (concl th)))) THEN
      UNDISCH_TAC `(z:real^N) IN ball(y,&2 * d)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN EXISTS_TAC `cball(y:real^N,d)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "k" THEN
        ASM_SIMP_TAC[REAL_MUL_LZERO; LIFT_NUM]]];
    ALL_TAC] THEN
  (* Cauchy-Schwarz on ball(y,2d) *)
  SUBGOAL_THEN
   `!g:real^N->real. (\z. lift(g z)) continuous_on cball(y,&2 * d)
                     ==> (\z. lift(g z)) integrable_on ball(y,&2 * d)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`\z:real^N. lift(g z)`; `y:real^N`; `&2 * d`]
      WANL_CONT_CBALL_INTEGRABLE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^N. lift((v:real^N->real) z - c)) continuous_on cball(y,&2 * d)`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z:real^N. lift((k:real^N->real) z)) continuous_on cball(y,&2 * d)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^N)` THEN
    EXPAND_TAC "k" THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->real`; `\z:real^N. (v:real^N->real) z - c`; `ball(y:real^N,&2 * d)`]
         WANL_INTEGRAL_CS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(integral (ball(y,&2 * d)) (\z. lift((k:real^N->real) z pow 2))) =
    K * inv d pow (dimindex(:N) + 2)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `drop(integral (:real^N) (\z. lift((k:real^N->real) z pow 2)))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC WAN_INTEGRAL_SUPPORT_SUBSET THEN
      EXISTS_TAC `cball(y:real^N,d)` THEN REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
        X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN EXPAND_TAC "k" THEN
        ASM_SIMP_TAC[REAL_POW_ZERO; ARITH_EQ; LIFT_NUM]];
      MATCH_MP_TAC(MESON[LIFT_DROP] `(x:real^1) = lift a ==> drop x = a`) THEN
      MATCH_MP_TAC INTEGRAL_UNIQUE THEN EXPAND_TAC "k" THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun u -> u = `K:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN ACCEPT_TAC]);;

(* Derivatives of smooth harmonic functions are harmonic.                    *)

let WANL_LLAP_PARTIAL = prove
 (`!(s:real^N->bool) (f:real^N->real) x.
        open s /\ x IN s /\ smooth_map_on s (\z. lift(f z))
        ==> llap (\z. mat 1) f x =
            sum(1..dimindex(:N))
              (\i. drop(partial_derivative i (partial_derivative i (\z. lift(f z))) x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real`; `x:real^N`] LLAP_FLAT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[PARTIAL_DERIVATIVE_ALT]);;

let WANL_DPART_HARMONIC = prove
 (`!(s:real^N->bool) (h:real^N->real) j x.
        open s /\ smooth_map_on s (\x. lift(h x)) /\
        (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0) /\ x IN s /\
        1 <= j /\ j <= dimindex(:N)
        ==> smooth_map_on s (\x. lift(wan_dpart j h x)) /\
            llap (\y:real^N. mat 1) (wan_dpart j h) x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `H = \x:real^N. lift((h:real^N->real) x)` THEN
  SUBGOAL_THEN `(\x:real^N. lift(wan_dpart j h x)) = partial_derivative j H` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[FUN_EQ_THM; wan_dpart; LIFT_DROP; partial_derivative];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. smooth_map_on s (partial_derivative k (H:real^N->real^1))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_PARTIAL_DERIVATIVE THEN
    EXPAND_TAC "H" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `wan_dpart j (h:real^N->real)`; `x:real^N`]
         WANL_LLAP_PARTIAL) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> partial_derivative i (partial_derivative i (partial_derivative j H)) x =
            partial_derivative j (partial_derivative i (partial_derivative i (H:real^N->real^1))) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `partial_derivative i (partial_derivative j (partial_derivative i (H:real^N->real^1))) x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "H" THEN ASM_MESON_TAC[smooth_map_on];
      MATCH_MP_TAC PARTIAL_DERIVATIVE_SYM THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[smooth_map_on]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..dimindex(:N))
      (\i. drop(partial_derivative i (partial_derivative i (partial_derivative j H)) x)) =
    drop(vsum(1..dimindex(:N))
      (\i. partial_derivative i (partial_derivative i (partial_derivative j (H:real^N->real^1))) x))`
  SUBST1_TAC THENL [REWRITE_TAC[DROP_VSUM; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[DROP_VEC] `(x:real^1) = vec 0 ==> drop x = &0`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum(1..dimindex(:N))
     (\i. partial_derivative j (partial_derivative i (partial_derivative i (H:real^N->real^1))) x)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`j:num`; `\i. partial_derivative i (partial_derivative i (H:real^N->real^1))`;
                 `1..dimindex(:N)`; `x:real^N`] PARTIAL_DERIVATIVE_VSUM) THEN
  REWRITE_TAC[ETA_AX; FINITE_NUMSEG] THEN ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `partial_derivative j (\z:real^N. vec 0:real^1) x` THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[PARTIAL_DERIVATIVE_CONST]] THEN
  MATCH_MP_TAC PARTIAL_DERIVATIVE_LOCAL_OPEN THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VSUM; o_DEF; DROP_VEC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real`; `z:real^N`] WANL_LLAP_PARTIAL) THEN
  EXPAND_TAC "H" THEN ASM_SIMP_TAC[]);;

(* The mean minimises the mean-square deviation.                             *)

let WANL_MEAN_MIN = prove
 (`!(G:real^N->real^K) a r c.
        &0 < r /\ G continuous_on cball(a,r)
        ==> drop(integral (ball(a,r))
                   (\x. lift(norm(G x - inv(measure(ball(a,r))) % integral (ball(a,r)) G)
                             pow 2))) <=
            drop(integral (ball(a,r)) (\x. lift(norm(G x - c) pow 2)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `m = inv(measure(ball(a:real^N,r))) % integral (ball(a,r)) (G:real^N->real^K)` THEN
  SUBGOAL_THEN `&0 < measure(ball(a:real^N,r))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURE_BALL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!f:real^N->real^1. f continuous_on cball(a,r) ==> f integrable_on ball(a,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`f:real^N->real^1`; `a:real^N`; `r:real`]
      WANL_CONT_CBALL_INTEGRABLE) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:real^N->real^K) integrable_on ball(a,r)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^N->real^K`; `a:real^N`; `r:real`] WANL_CONT_CBALL_INTEGRABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c':real^K. (\x. lift(norm((G:real^N->real^K) x - c') pow 2)) continuous_on cball(a,r)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. lift(norm((G:real^N->real^K) x - c) pow 2) =
        lift(norm(G x - m) pow 2) + &2 % lift((G x - m) dot (m - c)) +
        lift(norm(m - c:real^K) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM LIFT_CMUL; GSYM LIFT_ADD] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(G:real^N->real^K) x - c = (G x - m) + (m - c)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_POW_2; DOT_LADD; DOT_RADD] THEN REWRITE_TAC[DOT_SYM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. lift(((G:real^N->real^K) x - m) dot (m - c))) integrable_on ball(a,r)`
  ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL; INTEGRABLE_CONST;
               INTEGRAL_CONST; INTEGRABLE_ON_CONST; MEASURABLE_BALL] THEN
  SUBGOAL_THEN
   `integral (ball(a,r)) (\x. lift(((G:real^N->real^K) x - m) dot (m - c))) = vec 0`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\x. (G:real^N->real^K) x - m`; `ball(a:real^N,r)`;
                   `\v:real^K. lift(v dot (m - c))`] INTEGRAL_LINEAR) THEN
    REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_ON_CONST; MEASURABLE_BALL] THEN
      REWRITE_TAC[linear; DOT_LADD; DOT_LMUL; LIFT_ADD; LIFT_CMUL];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_ON_CONST; MEASURABLE_BALL; INTEGRAL_CONST_GEN] THEN
    EXPAND_TAC "m" THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                 VECTOR_SUB_REFL; DOT_LZERO; LIFT_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
  SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP; DROP_VEC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + &2 * &0 + y`) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2]);;

(* A Lipschitz bound from bounded partial derivatives on a ball.             *)

let WANL_FD_EXPAND_AT = prove
 (`!(g:real^N->real) z h.
        (\x. lift(g x)) differentiable (at z)
        ==> drop(frechet_derivative (\x. lift(g x)) (at z) h) =
            sum(1..dimindex(:N)) (\i. h$i * wan_dpart i g z)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative] o
    REWRITE_RULE[FRECHET_DERIVATIVE_WORKS]) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; DROP_VSUM; o_DEF] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  REWRITE_TAC[DROP_CMUL; wan_dpart]);;

let WANL_SMOOTH_LIPSCHITZ_BALL = prove
 (`!(U:real^N->bool) (g:real^N->real) a rho M.
        open U /\ ball(a,rho) SUBSET U /\ smooth_map_on U (\x. lift(g x)) /\
        (!z i. z IN ball(a,rho) /\ 1 <= i /\ i <= dimindex(:N) ==> abs(wan_dpart i g z) <= M)
        ==> !x. x IN ball(a,rho) ==> abs(g x - g a) <= &(dimindex(:N)) * M * norm(x - a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real^N) IN ball(a,rho)` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN ball(a,rho)` THEN REWRITE_TAC[IN_BALL; DIST_REFL] THEN
    MP_TAC(ISPECL [`a:real^N`; `x:real^N`] DIST_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN ball(a:real^N,rho) ==> (\x. lift((g:real^N->real) x)) differentiable (at z)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `U:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift((g:real^N->real) x)`;
                 `\z. frechet_derivative (\x. lift((g:real^N->real) x)) (at z)`;
                 `ball(a:real^N,rho)`; `&(dimindex(:N)) * M`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_BALL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [has_derivative] o
      REWRITE_RULE[FRECHET_DERIVATIVE_WORKS] o C MATCH_MP (ASSUME `(z:real^N) IN ball(a,rho)`)) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP ONORM) THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `h:real^N` THEN REWRITE_TAC[NORM_1] THEN
    ASM_SIMP_TAC[WANL_FD_EXPAND_AT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((h:real^N)$i * wan_dpart i (g:real^N->real) z))` THEN
    REWRITE_TAC[SUM_ABS_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. norm(h:real^N) * M)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[COMPONENT_LE_NORM];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `a:real^N`]) THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT; REAL_MUL_ASSOC]);;

(* Squares of continuous functions are integrable on balls.                 *)

let WANL_SQ_CONT_INTEGRABLE = prove
 (`!(f:real^N->real) y d.
        (\z. lift(f z)) continuous_on cball(y,d)
        ==> (\z. lift(f z pow 2)) integrable_on ball(y,d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^N. lift(f z pow 2)`; `y:real^N`; `d:real`]
         WANL_CONT_CBALL_INTEGRABLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[o_DEF];
    SIMP_TAC[]]);;

(* One constant for all coordinate directions.                               *)

let WANL_DPART_BOUND_UNIFORM = prove
 (`?K. &0 <= K /\
       !(U:real^N->bool) (v:real^N->real) y d c i.
          open U /\ smooth_map_on U (\x. lift(v x)) /\
          (!x. x IN U ==> llap (\z:real^N. mat 1) v x = &0) /\
          &0 < d /\ cball(y,&2 * d) SUBSET U /\ 1 <= i /\ i <= dimindex(:N)
          ==> wan_dpart i v y pow 2 <=
              K * inv(d) pow (dimindex(:N) + 2) *
              drop(integral (ball(y,&2 * d)) (\z. lift((v z - c) pow 2)))`,
  MP_TAC(INST_TYPE [`:N`,`:N`] WANL_HARMONIC_DPART_BOUND) THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Kf:num->real`) THEN
  EXISTS_TAC `sum(1..dimindex(:N)) Kf` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(Kf:num->real) i * inv(d) pow (dimindex(:N) + 2) *
              drop(integral (ball(y,&2 * d)) (\z. lift(((v:real^N->real) z - c) pow 2)))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`Kf:num->real`; `sum(1..dimindex(:N)) Kf`; `1..dimindex(:N)`]
           SUM_POS_BOUND) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; REAL_LE_REFL; IN_NUMSEG];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
      MATCH_MP_TAC WANL_SQ_CONT_INTEGRABLE THEN
      REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `U:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]]]);;

(* The gradient of a smooth harmonic function.                               *)

let WANL_GRAD_FACTS = prove
 (`!(s:real^N->bool) (h:real^N->real).
        open s /\ smooth_map_on s (\x. lift(h x)) /\
        (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0)
        ==> smooth_map_on s (wan_grad h) /\
            (!x j. 1 <= j /\ j <= dimindex(:N) ==> wan_grad h x$j = wan_dpart j h x) /\
            (!j. 1 <= j /\ j <= dimindex(:N)
                 ==> smooth_map_on s (\x. lift(wan_dpart j h x)) /\
                     (!x. x IN s ==> llap (\y:real^N. mat 1) (wan_dpart j h) x = &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= dimindex(:N)
        ==> smooth_map_on s (\x. lift(wan_dpart j h x)) /\
            (!x. x IN s ==> llap (\y:real^N. mat 1) (wan_dpart j h) x = &0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN `(\x:real^N. lift(wan_dpart j h x)) =
                    (\x. frechet_derivative (\y. lift((h:real^N->real) y)) (at x) (basis j))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_dpart; LIFT_DROP]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real`; `j:num`; `x:real^N`]
             WANL_DPART_HARMONIC) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[wan_grad; LAMBDA_BETA] THEN
  SUBGOAL_THEN `wan_grad (h:real^N->real) =
                (\x. (lambda k. drop((\k x. lift(wan_dpart k h x)) k x)):real^N)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; wan_grad; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LAMBDA THEN ASM_SIMP_TAC[]);;

(* Oscillation of the gradient at comparable radii.                          *)

let WANL_GRAD_OSC_LARGE = prove
 (`!(s:real^N->bool) (h:real^N->real) a r rho.
        open s /\ &0 < rho /\ r / &4 < rho /\ rho <= r /\ cball(a,r) SUBSET s /\
        smooth_map_on s (\x. lift(h x)) /\
        (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0)
        ==> drop(integral (ball(a,rho))
                   (\x. lift(norm(wan_grad h x - inv(measure(ball(a,rho))) %
                                    integral (ball(a,rho)) (wan_grad h)) pow 2))) <=
            &4 pow (dimindex(:N) + 2) * (rho / r) pow (dimindex(:N) + 2) *
            drop(integral (ball(a,r))
                   (\x. lift(norm(wan_grad h x - inv(measure(ball(a,r))) %
                                    integral (ball(a,r)) (wan_grad h)) pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real`] WANL_GRAD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = inv(measure(ball(a:real^N,r))) % integral (ball(a,r)) (wan_grad h)` THEN
  SUBGOAL_THEN `(wan_grad h:real^N->real^N) continuous_on cball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t <= r ==> (\x. lift(norm(wan_grad h x - c:real^N) pow 2)) integrable_on ball(a:real^N,t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lift(norm(wan_grad h x - c:real^N) pow 2)`; `a:real^N`; `t:real`]
           WANL_CONT_CBALL_INTEGRABLE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(a,rho)) (\x. lift(norm(wan_grad h x - c:real^N) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_MEAN_MIN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(a,r)) (\x. lift(norm(wan_grad h x - c:real^N) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[SUBSET_BALL; REAL_LE_REFL; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&4 * x / r = (&4 * x) / r`] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LIFT_DROP; REAL_LE_POW_2]]);;

(* Oscillation of the gradient at small radii.                               *)

let WANL_GRAD_OSC_SMALL = prove
 (`?C. &0 < C /\
       !(s:real^N->bool) (h:real^N->real) a r rho.
          open s /\ &0 < rho /\ rho <= r / &4 /\ cball(a,r) SUBSET s /\
          smooth_map_on s (\x. lift(h x)) /\
          (!x. x IN s ==> llap (\y:real^N. mat 1) h x = &0)
          ==> drop(integral (ball(a,rho))
                     (\x. lift(norm(wan_grad h x - inv(measure(ball(a,rho))) %
                                      integral (ball(a,rho)) (wan_grad h)) pow 2))) <=
              C * (rho / r) pow (dimindex(:N) + 2) *
              drop(integral (ball(a,r))
                     (\x. lift(norm(wan_grad h x - inv(measure(ball(a,r))) %
                                      integral (ball(a,r)) (wan_grad h)) pow 2)))`,
  X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WANL_DPART_BOUND_UNIFORM) THEN
  ABBREV_TAC `mu = measure(ball(vec 0:real^N,&1))` THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN REWRITE_TAC[MEASURE_BALL_POS] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(dimindex(:N))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `mu * &(dimindex(:N)) pow 3 * (K + &1) * &4 pow (dimindex(:N) + 2)` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real`] WANL_GRAD_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "comp") (LABEL_TAC "dh"))) THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = inv(measure(ball(a:real^N,r))) % integral (ball(a,r)) (wan_grad h)` THEN
  ABBREV_TAC `E = drop(integral (ball(a:real^N,r)) (\x. lift(norm(wan_grad h x - c) pow 2)))` THEN
  SUBGOAL_THEN `(wan_grad h:real^N->real^N) continuous_on cball(a,r)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t (c':real^N). t <= r
          ==> (\x. lift(norm(wan_grad h x - c') pow 2)) integrable_on ball(a:real^N,t)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lift(norm(wan_grad h x - c':real^N) pow 2)`; `a:real^N`; `t:real`]
           WANL_CONT_CBALL_INTEGRABLE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LIFT_DROP; REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `M = sqrt(K * inv(r / &4) pow (dimindex(:N) + 2) * E)` THEN
  SUBGOAL_THEN `&0 <= K * inv(r / &4) pow (dimindex(:N) + 2) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* A: the second derivatives are bounded by M on ball(a,r/4) *)
  SUBGOAL_THEN
   `!z i j. z IN ball(a:real^N,r / &4) /\ 1 <= i /\ i <= dimindex(:N) /\
            1 <= j /\ j <= dimindex(:N)
            ==> abs(wan_dpart i (wan_dpart j h) z) <= M`
  (LABEL_TAC "A") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN
    USE_THEN "dh" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`))) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K * inv(r / &4) pow (dimindex(:N) + 2) *
                drop(integral (ball(z:real^N,&2 * r / &4))
                       (\q. lift((wan_dpart j (h:real^N->real) q - (c:real^N)$j) pow 2)))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun u -> u = `K:real`)) (concl th) && is_forall(concl th))) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^N,r)` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^N) IN ball(a,r / &4)` THEN
      REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN DISCH_TAC THEN
      X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`a:real^N`; `z:real^N`; `q:real^N`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "E" THEN
    SUBGOAL_THEN `(\q:real^N. lift((wan_dpart j (h:real^N->real) q - (c:real^N)$j) pow 2)) continuous_on cball(a,r)`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_SUB] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (ball(a:real^N,r)) (\q. lift((wan_dpart j (h:real^N->real) q - (c:real^N)$j) pow 2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^N) IN ball(a,r / &4)` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_TAC THEN
        X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real^N`; `z:real^N`; `q:real^N`] DIST_TRIANGLE) THEN
        ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`\q:real^N. lift((wan_dpart j (h:real^N->real) q - (c:real^N)$j) pow 2)`; `z:real^N`;
                       `&2 * r / &4`] WANL_CONT_CBALL_INTEGRABLE) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^N) IN ball(a,r / &4)` THEN
        REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN DISCH_TAC THEN
        X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real^N`; `z:real^N`; `q:real^N`] DIST_TRIANGLE) THEN
        ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`\q:real^N. lift((wan_dpart j (h:real^N->real) q - (c:real^N)$j) pow 2)`; `a:real^N`;
                       `r:real`] WANL_CONT_CBALL_INTEGRABLE) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\q:real^N. lift((wan_dpart j (h:real^N->real) q - (c:real^N)$j) pow 2)`; `a:real^N`;
                     `r:real`] WANL_CONT_CBALL_INTEGRABLE) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    USE_THEN "comp" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th (CONJ (ASSUME `1 <= j`)
      (ASSUME `j <= dimindex(:N)`)))]) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM];
    ALL_TAC] THEN
  (* B: Lipschitz bounds for the components on ball(a,rho) *)
  SUBGOAL_THEN
   `!x j. x IN ball(a:real^N,rho) /\ 1 <= j /\ j <= dimindex(:N)
          ==> abs(wan_dpart j h x - wan_dpart j h a) <= &(dimindex(:N)) * M * rho`
  (LABEL_TAC "B") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "dh" (MP_TAC o C MATCH_MP (CONJ (ASSUME `1 <= j`) (ASSUME `j <= dimindex(:N)`))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `wan_dpart j (h:real^N->real)`; `a:real^N`; `r / &4`;
                   `M:real`] WANL_SMOOTH_LIPSCHITZ_BALL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(a:real^N,r)` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
        X_GEN_TAC `q:real^N` THEN ASM_REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "A" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN ball(a,rho)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN ball(a,rho)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`a:real^N`; `x:real^N`] NORM_SUB) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* C: the pointwise bound for the gradient *)
  SUBGOAL_THEN
   `!x. x IN ball(a:real^N,rho)
        ==> norm(wan_grad h x - wan_grad h a) pow 2 <=
            &(dimindex(:N)) * (&(dimindex(:N)) * M * rho) pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_POW_2; dot] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. (&(dimindex(:N)) * M * rho) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[GSYM REAL_POW_2; VECTOR_SUB_COMPONENT] THEN
      USE_THEN "comp" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ (ASSUME `1 <= j`)
        (ASSUME `j <= dimindex(:N)`))]) THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
      SUBGOAL_THEN `&0 <= &(dimindex(:N)) * M * rho` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the integral estimate *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(a:real^N,rho))
                     (\x. lift(norm(wan_grad h x - wan_grad h a) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WANL_MEAN_MIN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(a:real^N,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (ball(a:real^N,rho))
                     (\x. lift(&(dimindex(:N)) * (&(dimindex(:N)) * M * rho) pow 2)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_ON_CONST; MEASURABLE_BALL] THEN
    MP_TAC(ISPECL [`rho:real`; `wan_grad h (a:real^N)`] (ASSUME
       `!t (c':real^N). t <= r
          ==> (\x. lift(norm(wan_grad h x - c') pow 2)) integrable_on ball(a:real^N,t)`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SIMP_TAC[INTEGRAL_CONST_GEN; MEASURABLE_BALL; DROP_CMUL; LIFT_DROP] THEN
  SUBGOAL_THEN `measure(ball(a:real^N,rho)) = rho pow dimindex(:N) * mu` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `rho:real`; `&1`] MEASURE_BALL_SCALING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "mu" THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC WANL_MEASURE_BALL_TRANSLATE;
    ALL_TAC] THEN
  SUBGOAL_THEN `M pow 2 = K * inv(r / &4) pow (dimindex(:N) + 2) * E` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(rho pow dimindex(:N) * mu) * &(dimindex(:N)) * (&(dimindex(:N)) * M * rho) pow 2 =
    (mu * &(dimindex(:N)) pow 3 * K * &4 pow (dimindex(:N) + 2)) *
    (rho / r) pow (dimindex(:N) + 2) * E`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_INV_DIV; REAL_POW_DIV; REAL_POW_ADD] THEN
    SUBGOAL_THEN `~(r pow dimindex(:N) = &0) /\ ~(r = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC(`r pow dimindex(:N)`,`q:real`) THEN
    SPEC_TAC(`rho pow dimindex(:N)`,`p:real`) THEN
    SPEC_TAC(`&4 pow dimindex(:N)`,`f:real`) THEN
    REPEAT GEN_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]);;

let WAN_HARM_GRAD_OSC = prove
 (`!n:N->bool. WAN_HARM_GRAD_OSC_STATEMENT n`,
  GEN_TAC THEN REWRITE_TAC[WAN_HARM_GRAD_OSC_STATEMENT] THEN
  X_CHOOSE_THEN `C1:real` STRIP_ASSUME_TAC (INST_TYPE [`:N`,`:N`] WANL_GRAD_OSC_SMALL) THEN
  SUBGOAL_THEN `&0 < &4 pow (dimindex(:N) + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `C1 + &4 pow (dimindex(:N) + 2)` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `E = drop(integral (ball(a:real^N,r))
              (\x. lift(norm(wan_grad h x - inv(measure(ball(a,r))) %
                               integral (ball(a,r)) (wan_grad h)) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `h:real^N->real`] WANL_GRAD_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lift(norm(wan_grad h x - inv(measure(ball(a:real^N,r))) %
                               integral (ball(a,r)) (wan_grad h)) pow 2)`; `a:real^N`; `r:real`]
           WANL_CONT_CBALL_INTEGRABLE) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    REWRITE_TAC[NORM_POW_2] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (rho / r) pow (dimindex(:N) + 2) * E` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `rho <= r / &4` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `C1 * (rho / r) pow (dimindex(:N) + 2) * E` THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 pow (dimindex(:N) + 2) * (rho / r) pow (dimindex(:N) + 2) * E` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "E" THEN MATCH_MP_TAC WANL_GRAD_OSC_LARGE THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]]);;

