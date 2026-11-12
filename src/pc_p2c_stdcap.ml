(* ========================================================================= *)
(* Unit pc_p2c_stdcap (Part 2C; for MT Thm 12.32, pc_p2c_stdc4): an          *)
(* explicit (C,eps)-cap in R^3 (rfs_cap, ball case) for a metric g with two  *)
(* radial necks, from uniform bounds on g, R and the derivatives of R.       *)
(* The unit is below the interface files: no standard-solution names.        *)
(*  - The ball chart glues c y near 0 to a radial map E y = P(|y|)/|y| y     *)
(*    (the inner neck seen through a sphere diffeomorphism) with a smooth    *)
(*    step in |y|; the glued profile has a positive derivative, so the       *)
(*    chart is a diffeomorphism (SCHI_INJ_DIFFEO).                           *)
(*  - The constants: diameter by Euclidean segments, volume against the      *)
(*    flat volume, noncollapsing from the Euclidean ball of radius r/sqrt M  *)
(*    inside a metric ball, which stays in the core or in a slab of the      *)
(*    inner neck (apx_eng_n2).                                               *)
(* ========================================================================= *)

needs "src/pc_rfs_geom.ml";;
needs "src/pc_smt_radial.ml";;
needs "src/ns_cutoff.ml";;
needs "src/pc_apx_chain.ml";;
needs "src/pc_grg_area.ml";;
needs "src/pc_grg_vol.ml";;
needs "src/pc_sch_isoext.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The gluing step and the glued profile.  stdcap_step r is                  *)
(* smooth_step((r^2 - 1/4) 36/7): 0 for abs r <= 1/2, 1 for abs r >= 2/3,     *)
(* smooth in the point of R^3 through |y|^2, with a nonnegative derivative   *)
(* for r >= 0.  For P with P' > 0 on (1/4,2) and c = P(1/2)/2 the profile     *)
(* (1 - s r) c r + s r P(r) has a positive derivative on [0,2).              *)
(* ------------------------------------------------------------------------- *)

let stdcap_step = new_definition
 `stdcap_step (r:real) = smooth_step((r pow 2 - &1 / &4) * &36 / &7)`;;

let stdcap_prof = new_definition
 `stdcap_prof (c:real) (P:real->real) (r:real) =
    (&1 - stdcap_step r) * c * r + stdcap_step r * P r`;;

let STDCAP_STEP_0 = prove
 (`!r. abs r <= &1 / &2 ==> stdcap_step r = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stdcap_step] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
  SUBGOAL_THEN `r pow 2 <= (&1 / &2) pow 2` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let STDCAP_STEP_1 = prove
 (`!r. &2 / &3 <= abs r ==> stdcap_step r = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stdcap_step] THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
  SUBGOAL_THEN `(&2 / &3) pow 2 <= r pow 2` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let STDCAP_STEP_BOUNDS = prove
 (`!r. &0 <= stdcap_step r /\ stdcap_step r <= &1`,
  REWRITE_TAC[stdcap_step; SMOOTH_STEP_BOUNDS]);;

let STDCAP_STEP_MONO = prove
 (`!r s. &0 <= r /\ r <= s ==> stdcap_step r <= stdcap_step s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stdcap_step] THEN MATCH_MP_TAC SMOOTH_STEP_MONO THEN
  SUBGOAL_THEN `r pow 2 <= s pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]);;

(* smooth_step has a nonnegative derivative everywhere (the argument of     *)
(* P2C_S1_DERIV, pc_p2c_stdinit, for s = UNIV).                              *)

let STDCAP_SS_DERIV = prove
 (`!u. (smooth_step has_real_derivative real_derivative smooth_step u) (atreal u) /\
       &0 <= real_derivative smooth_step u`,
  SUBGOAL_THEN `!u. (smooth_step has_real_derivative real_derivative smooth_step u) (atreal u)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `smooth_step real_differentiable (atreal u)` MP_TAC THENL
     [REWRITE_TAC[REAL_DIFFERENTIABLE_AT] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^1)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_STEP_SMOOTH];
      REWRITE_TAC[real_differentiable; real_derivative] THEN
      DISCH_TAC THEN CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`smooth_step`; `real_derivative smooth_step`; `(:real)`]
                HAS_REAL_DERIVATIVE_INCREASING) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_UNIV; IN_UNIV; WITHINREAL_UNIV] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM; EXTENSION; IN_UNIV; IN_SING] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `a + &1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[SMOOTH_STEP_MONO]);;

let STDCAP_STEP_DERIV = prove
 (`!r. ?d. (stdcap_step has_real_derivative d) (atreal r) /\ (&0 <= r ==> &0 <= d)`,
  GEN_TAC THEN
  EXISTS_TAC `(&72 / &7 * r) *
              real_derivative smooth_step ((r pow 2 - &1 / &4) * &36 / &7)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `stdcap_step = (\x. smooth_step ((\r. (r pow 2 - &1 / &4) * &36 / &7) x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stdcap_step]; ALL_TAC] THEN
    MP_TAC(INST [`real_derivative smooth_step`,`g':real->real`; `&72 / &7 * r`,`f':real`]
            (ISPECL [`\r. (r pow 2 - &1 / &4) * &36 / &7`; `smooth_step`]
                    HAS_REAL_DERIVATIVE_CHAIN_UNIV)) THEN
    REWRITE_TAC[STDCAP_SS_DERIV] THEN DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MP_TAC(REAL_DIFF_CONV `((\r. (r pow 2 - &1 / &4) * &36 / &7) has_real_derivative f)
                               (atreal r)`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
      BETA_TAC THEN SIMP_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[STDCAP_SS_DERIV] THEN
    ASM_REAL_ARITH_TAC]);;

let STDCAP_STEP_SMOOTH = prove
 (`smooth_map_on (:real^3) (\z. lift(stdcap_step(norm z)))`,
  REWRITE_TAC[stdcap_step] THEN
  MP_TAC(ISPECL [`(:real^3)`;
                 `\z:real^3. (&36 / &7) % (lift(norm z pow 2) - lift(&1 / &4))`]
                SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
    REWRITE_TAC[OPEN_UNIV] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_CONST] THEN
    MP_TAC(ISPECL [`(:real^3)`; `\z:real^3. z`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    REWRITE_TAC[OPEN_UNIV; SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB; LIFT_DROP] THEN REAL_ARITH_TAC);;

let STDCAP_PROF_SMALL = prove
 (`!c P r. abs r <= &1 / &2 ==> stdcap_prof c P r = c * r`,
  SIMP_TAC[stdcap_prof; STDCAP_STEP_0] THEN REAL_ARITH_TAC);;

let STDCAP_PROF_BIG = prove
 (`!c P r. &2 / &3 <= abs r ==> stdcap_prof c P r = P r`,
  SIMP_TAC[stdcap_prof; STDCAP_STEP_1] THEN REAL_ARITH_TAC);;

(* The profile hypotheses used below.                                        *)

let STDCAP_P_MONO = prove
 (`!P P' a b.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &1 / &4 < a /\ a <= b /\ b < &2
     ==> P a <= P b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_INCREASING_IMP THEN
  MAP_EVERY EXISTS_TAC [`P':real->real`; `real_interval[a,b]`] THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THEN X_GEN_TAC `x:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let STDCAP_PROF_DERIV = prove
 (`!P P' r.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ &0 <= r /\ r < &2
     ==> ?d. (stdcap_prof (P(&1 / &2) / &2) P has_real_derivative d) (atreal r) /\ &0 < d`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `c = P(&1 / &2) / &2` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r < &1 / &2` THENL
   [EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    MAP_EVERY EXISTS_TAC [`\s:real. c * s`; `&1 / &2 - r`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC STDCAP_PROF_SMALL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(REAL_DIFF_CONV `((\s. c * s) has_real_derivative f) (atreal r)`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:real`) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC `r:real` STDCAP_STEP_DERIV) THEN
  DISCH_THEN(X_CHOOSE_THEN `ds:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= ds` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `(&1 - stdcap_step r) * c + stdcap_step r * P' r + ds * (P r - c * r)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `((\s. &1 - stdcap_step s) has_real_derivative --ds) (atreal r)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\s:real. &1`; `&0`; `stdcap_step`; `ds:real`; `atreal r`]
                    HAS_REAL_DERIVATIVE_SUB) THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_SUB_LZERO; ETA_AX];
      ALL_TAC] THEN
    SUBGOAL_THEN `((\s:real. c * s) has_real_derivative c) (atreal r)` ASSUME_TAC THENL
     [MP_TAC(REAL_DIFF_CONV `((\s. c * s) has_real_derivative f) (atreal r)`) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `((\s. (&1 - stdcap_step s) * (c * s)) has_real_derivative
                   (&1 - stdcap_step r) * c + --ds * (c * r)) (atreal r)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\s. &1 - stdcap_step s`; `--ds`; `\s:real. c * s`; `c:real`; `r:real`]
                    HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((\s. stdcap_step s * (P:real->real) s) has_real_derivative
                   stdcap_step r * (P':real->real) r + ds * P r) (atreal r)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`stdcap_step`; `ds:real`; `P:real->real`; `(P':real->real) r`; `r:real`]
                    HAS_REAL_DERIVATIVE_MUL_ATREAL) THEN
      ASM_REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\s. (&1 - stdcap_step s) * (c * s)`;
                   `(&1 - stdcap_step r) * c + --ds * (c * r)`;
                   `\s. stdcap_step s * (P:real->real) s`;
                   `stdcap_step r * (P':real->real) r + ds * P r`; `atreal r`]
                  HAS_REAL_DERIVATIVE_ADD) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; stdcap_prof] THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* positivity *)
  SUBGOAL_THEN `&2 * c <= (P:real->real) r` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN
    MATCH_MP_TAC STDCAP_P_MONO THEN EXISTS_TAC `P':real->real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ds * (P r - c * r)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c * r <= c * &2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `r:real` STDCAP_STEP_BOUNDS) THEN STRIP_TAC THEN
  ABBREV_TAC `m = min c ((P':real->real) r)` THEN
  SUBGOAL_THEN `&0 < m /\ m <= c /\ m <= (P':real->real) r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 - stdcap_step r) * (c - m) /\
                &0 <= stdcap_step r * ((P':real->real) r - m)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The glued ball chart stdcap_glue c P z = (B(|z|)/|z|) z,                  *)
(* B the glued profile: c z for |z| < 1/2, P(|z|)/|z| z for |z| >= 2/3.  It  *)
(* is smooth, injective with invertible derivative on ball(0,2), hence a     *)
(* ball chart of R^3, with ball, closed ball and sphere of radius 1 mapped   *)
(* onto those of radius P(1).                                                 *)
(* ------------------------------------------------------------------------- *)

let stdcap_glue = new_definition
 `stdcap_glue (c:real) (P:real->real) (z:real^3) =
    (stdcap_prof c P (norm z) / norm z) % z`;;

(* The derivative of the norm (a copy of P2C_NORM_DERIV, pc_p2c_stdinit,     *)
(* which lies above the interface files).                                    *)

let STDCAP_NORM_DERIV = prove
 (`!x:real^N.
     ~(x = vec 0)
     ==> ((\y. lift(norm y)) has_derivative (\h. lift((x dot h) / norm x))) (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N) pow 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sqrt`; `inv(&2 * sqrt(norm(x:real^N) pow 2))`;
                 `\z:real^N. lift(norm z pow 2)`; `\h:real^N. &2 % lift(x dot h)`;
                 `x:real^N`] LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
  ASM_SIMP_TAC[LIFT_DROP; HAS_DERIVATIVE_SQNORM_AT; HAS_REAL_DERIVATIVE_SQRT] THEN
  SIMP_TAC[POW_2_SQRT; NORM_POS_LE] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
  GEN_TAC THEN SUBGOAL_THEN `~(norm(x:real^N) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

let STDCAP_PROF_DERIVS = prove
 (`!P P'.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2)
     ==> ?D. !r. &0 <= r /\ r < &2
                 ==> (stdcap_prof (P(&1 / &2) / &2) P has_real_derivative D r) (atreal r) /\
                     &0 < D r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `r:real` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC STDCAP_PROF_DERIV THEN EXISTS_TAC `P':real->real` THEN ASM_REWRITE_TAC[]);;

let STDCAP_PROF_STRICT = prove
 (`!P P' r s.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ &0 <= r /\ r < s /\ s < &2
     ==> stdcap_prof (P(&1 / &2) / &2) P r < stdcap_prof (P(&1 / &2) / &2) P s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_PROF_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real->real` (LABEL_TAC "D")) THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_STRICTLY_INCREASING_IMP THEN
  EXISTS_TAC `D:real->real` THEN ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    USE_THEN "D" (MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    USE_THEN "D" (MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]);;

let STDCAP_PROF_ZERO = prove
 (`!c P. stdcap_prof c P (&0) = &0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`c:real`; `P:real->real`; `&0`] STDCAP_PROF_SMALL) THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[REAL_MUL_RZERO]);;

let STDCAP_PROF_POS = prove
 (`!P P' r.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ &0 < r /\ r < &2
     ==> &0 < stdcap_prof (P(&1 / &2) / &2) P r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P(&1 / &2) / &2`; `P:real->real`] STDCAP_PROF_ZERO) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC STDCAP_PROF_STRICT THEN EXISTS_TAC `P':real->real` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL]);;

let STDCAP_PROF_CONT = prove
 (`!P P' b.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ b < &2
     ==> stdcap_prof (P(&1 / &2) / &2) P real_continuous_on real_interval[&0,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_PROF_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real->real` (LABEL_TAC "D")) THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[real_differentiable_on; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[real_differentiable] THEN
  EXISTS_TAC `(D:real->real) x` THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
  USE_THEN "D" (MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let STDCAP_GLUE_SMALL = prove
 (`!c P z. norm z < &1 / &2 ==> stdcap_glue c P z = c % z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stdcap_glue] THEN
  MP_TAC(SPECL [`c:real`; `P:real->real`; `norm(z:real^3)`] STDCAP_PROF_SMALL) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_ABS_NORM] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_EQ_0]; CONV_TAC REAL_FIELD]);;

let STDCAP_GLUE_BIG = prove
 (`!c P z. &2 / &3 <= norm z ==> stdcap_glue c P z = (P(norm z) / norm z) % z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stdcap_glue] THEN
  MP_TAC(SPECL [`c:real`; `P:real->real`; `norm(z:real^3)`] STDCAP_PROF_BIG) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let STDCAP_GLUE_NORM = prove
 (`!P P' z.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ norm z < &2
     ==> norm(stdcap_glue (P(&1 / &2) / &2) P z) =
         stdcap_prof (P(&1 / &2) / &2) P (norm z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stdcap_glue] THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; NORM_0; STDCAP_PROF_ZERO] THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`; `norm(z:real^3)`] STDCAP_PROF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD);;

let STDCAP_GLUE_INJ = prove
 (`!P P' z1 z2.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ norm z1 < &2 /\ norm z2 < &2 /\
     stdcap_glue (P(&1 / &2) / &2) P z1 = stdcap_glue (P(&1 / &2) / &2) P z2
     ==> z1 = z2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(z1:real^3) = norm(z2:real^3)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`P:real->real`; `P':real->real`; `z1:real^3`] STDCAP_GLUE_NORM) THEN
    MP_TAC(SPECL [`P:real->real`; `P':real->real`; `z2:real^3`] STDCAP_GLUE_NORM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `stdcap_prof (P(&1 / &2) / &2) P (norm(z1:real^3)) =
                  stdcap_prof (P(&1 / &2) / &2) P (norm(z2:real^3))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [MP_TAC(SPECL [`P:real->real`; `P':real->real`; `norm(z2:real^3)`; `norm(z1:real^3)`]
                   STDCAP_PROF_STRICT);
      MP_TAC(SPECL [`P:real->real`; `P':real->real`; `norm(z1:real^3)`; `norm(z2:real^3)`]
                   STDCAP_PROF_STRICT)] THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `z1:real^3 = vec 0` THENL
   [SUBGOAL_THEN `z2:real^3 = vec 0` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z1:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`; `norm(z1:real^3)`] STDCAP_PROF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `stdcap_glue (P(&1 / &2) / &2) P z1 = stdcap_glue (P(&1 / &2) / &2) P z2` THEN
  ASM_REWRITE_TAC[stdcap_glue; VECTOR_MUL_LCANCEL] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN
  MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let STDCAP_GLUE_SMOOTH = prove
 (`!c P.
     smooth_map_on (annulus (&1 / &4) (&2)) (\z:real^3. (P(norm z) / norm z) % z)
     ==> smooth_map_on (ball(vec 0,&2)) (stdcap_glue c P)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN REWRITE_TAC[OPEN_BALL] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  ASM_CASES_TAC `norm(x:real^3) < &1 / &2` THENL
   [EXISTS_TAC `ball(vec 0:real^3,&1 / &2)` THEN ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:real^3. c % z` THEN
    REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC STDCAP_GLUE_SMALL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_ID]];
    ALL_TAC] THEN
  EXISTS_TAC `annulus (&1 / &4) (&2):real^3->bool` THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  CONJ_TAC THENL [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z:real^3. drop(lift(&1) - lift(stdcap_step(norm z))) % (c % z) +
                         drop(lift(stdcap_step(norm z))) % ((P(norm z) / norm z) % z)` THEN
  REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[DROP_SUB; LIFT_DROP; stdcap_glue; stdcap_prof; VECTOR_MUL_ASSOC;
                GSYM VECTOR_ADD_RDISTRIB] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (annulus (&1 / &4) (&2))
                  (\z:real^3. lift(stdcap_step(norm z)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
    REWRITE_TAC[SUBSET_UNIV; STDCAP_STEP_SMOOTH];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[OPEN_ANNULUS; SMOOTH_MAP_ON_CONST];
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN REWRITE_TAC[OPEN_ANNULUS; SMOOTH_MAP_ON_ID]]);;

(* The linear maps h -> k h + (c (y0.h)/m) y0 (as STDS_LINEAR_RANK1 of      *)
(* pc_p2c_stdc3, which lies above the interface files).                      *)

let STDCAP_LINEAR_RANK1 = prove
 (`!k c (y0:real^N) m. linear (\h. k % h + (c * (y0 dot h) / m) % y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear; DOT_RADD; DOT_RMUL] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB; VECTOR_ADD_RDISTRIB;
              VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH `c * (a * x) * m = a * c * x * m`] THEN
  VECTOR_ARITH_TAC);;

let STDCAP_DET_NZ = prove
 (`!L:real^N->real^N. linear L /\ (!h. L h = vec 0 ==> h = vec 0)
                      ==> ~(det(matrix L) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `matrix(L:real^N->real^N)` HOMOGENEOUS_LINEAR_EQUATIONS_DET) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[]);;

(* The derivative of a radial map x -> q(|x|) x away from 0.                 *)

let STDCAP_RADIAL_VEC_DERIV = prove
 (`!(q:real->real) q' (z:real^N).
     ~(z = vec 0) /\ (q has_real_derivative q') (atreal (norm z))
     ==> ((\x. q(norm x) % x) has_derivative
          (\h. q(norm z) % h + (q' * (z dot h) / norm z) % z)) (at z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. (q:real->real)(norm x)`; `\h:real^N. q' * (z dot h) / norm z`;
                 `\x:real^N. x`; `\h:real^N. h`; `z:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[HAS_DERIVATIVE_ID] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`q:real->real`; `q':real`; `\y:real^N. lift(norm y)`;
                   `\h:real^N. lift((z dot h) / norm z)`; `z:real^N`]
                  LRG_HAS_DERIVATIVE_REAL_COMPOSE) THEN
    ASM_SIMP_TAC[LIFT_DROP; STDCAP_NORM_DERIV] THEN
    REWRITE_TAC[o_DEF; GSYM LIFT_CMUL] THEN SIMP_TAC[];
    BETA_TAC THEN SIMP_TAC[]]);;

let STDCAP_GLUE_DERIV = prove
 (`!P P' z.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\ norm z < &2
     ==> ?L. linear L /\ (stdcap_glue (P(&1 / &2) / &2) P has_derivative L) (at z) /\
             !h. L h = vec 0 ==> h = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_PROF_DERIVS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `D:real->real` (LABEL_TAC "D")) THEN
  ABBREV_TAC `c = (P:real->real)(&1 / &2) / &2` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:real^3) < &1 / &2` THENL
   [EXISTS_TAC `\h:real^3. c % h` THEN
    SIMP_TAC[LINEAR_COMPOSE_CMUL; LINEAR_ID] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`\x:real^3. c % x`; `&1 / &2 - norm(z:real^3)`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC STDCAP_GLUE_SMALL THEN
        MP_TAC(ISPECL [`w:real^3`; `z:real^3`] NORM_TRIANGLE_SUB) THEN
        UNDISCH_TAC `dist(w:real^3,z) < &1 / &2 - norm(z:real^3)` THEN
        REWRITE_TAC[dist] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID]];
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^3 = vec 0) /\ &0 < norm(z:real^3)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "D" (MP_TAC o SPEC `norm(z:real^3)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE]; STRIP_TAC] THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`; `norm(z:real^3)`] STDCAP_PROF_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\s. stdcap_prof c P s / s) has_real_derivative
     ((D:real->real)(norm(z:real^3)) * norm z - stdcap_prof c P (norm z) * &1) /
     norm z pow 2) (atreal (norm z))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`stdcap_prof c P`; `(D:real->real)(norm(z:real^3))`; `\s:real. s`; `&1`;
                   `norm(z:real^3)`] HAS_REAL_DERIVATIVE_DIV_ATREAL) THEN
    ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[ETA_AX]];
    ALL_TAC] THEN
  ABBREV_TAC `b1 = ((D:real->real)(norm(z:real^3)) * norm z - stdcap_prof c P (norm z) * &1) /
                   norm z pow 2` THEN
  MP_TAC(ISPECL [`\s. stdcap_prof c P s / s`; `b1:real`; `z:real^3`]
                STDCAP_RADIAL_VEC_DERIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `\h:real^3. (stdcap_prof c P (norm z) / norm z) % h + (b1 * (z dot h) / norm z) % z` THEN
  REWRITE_TAC[STDCAP_LINEAR_RANK1] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `stdcap_glue c P = (\x:real^3. (\s. stdcap_prof c P s / s) (norm x) % x)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; stdcap_glue]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_derivative")) (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `h:real^3` THEN BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) dot h = &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. (z:real^3) dot v`) THEN
    REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RZERO; DOT_SQUARE_NORM] THEN
    SUBGOAL_THEN `stdcap_prof c P (norm z) / norm z * ((z:real^3) dot h) +
                  (b1 * (z dot h) / norm z) * norm z pow 2 =
                  (z dot h) * (D:real->real)(norm z)` SUBST1_TAC THENL
     [EXPAND_TAC "b1" THEN UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  UNDISCH_TAC `(stdcap_prof c P (norm z) / norm z) % (h:real^3) +
               (b1 * ((z:real^3) dot h) / norm z) % z = vec 0` THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID;
                  VECTOR_MUL_EQ_0] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]);;

let STDCAP_P_ONE = prove
 (`!P P'.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2)
     ==> &0 < P(&1) /\ stdcap_prof (P(&1 / &2) / &2) P (&1) = P(&1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(P:real->real)(&1 / &2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDCAP_P_MONO THEN EXISTS_TAC `P':real->real` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC STDCAP_PROF_BIG THEN REAL_ARITH_TAC]);;

let STDCAP_GLUE_IMAGE_BALL = prove
 (`!P P'.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2)
     ==> IMAGE (stdcap_glue (P(&1 / &2) / &2) P) (ball(vec 0,&1)) = ball(vec 0,P(&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_P_ONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = (P:real->real)(&1 / &2) / &2` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`P:real->real`; `P':real->real`; `z:real^3`] STDCAP_GLUE_NORM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `stdcap_prof c P (&1)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_LE_REFL]] THEN
    MP_TAC(SPECL [`P:real->real`; `P':real->real`; `norm(z:real^3)`; `&1`]
                 STDCAP_PROF_STRICT) THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL [REAL_ARITH_TAC; SIMP_TAC[]];
    DISCH_TAC] THEN
  ASM_CASES_TAC `x:real^3 = vec 0` THENL
   [EXISTS_TAC `vec 0:real^3` THEN ASM_REWRITE_TAC[NORM_0; stdcap_glue; VECTOR_MUL_RZERO] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`stdcap_prof c P`; `&0`; `&1`; `norm(x:real^3)`] REAL_IVT_INCREASING) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS; STDCAP_PROF_ZERO; NORM_POS_LE] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC STDCAP_PROF_CONT THEN EXISTS_TAC `P':real->real` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < r /\ r < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `r = &0` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `stdcap_prof c P (&0) = norm(x:real^3)` THEN
      REWRITE_TAC[STDCAP_PROF_ZERO] THEN ASM_MESON_TAC[NORM_EQ_0];
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `r = &1` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `(r / norm(x:real^3)) % x` THEN
  SUBGOAL_THEN `norm((r / norm(x:real^3)) % x) = r` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[stdcap_glue; VECTOR_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

let STDCAP_GLUE_IMAGE_SPHERE = prove
 (`!P P'.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2)
     ==> IMAGE (stdcap_glue (P(&1 / &2) / &2) P) (sphere(vec 0,&1)) = sphere(vec 0,P(&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_P_ONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^3. norm z = &1 ==> stdcap_glue (P(&1 / &2) / &2) P z = P(&1) % z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[stdcap_glue; REAL_DIV_1]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[] THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN EXISTS_TAC `inv((P:real->real)(&1)) % (x:real^3)` THEN
    SUBGOAL_THEN `norm(inv((P:real->real)(&1)) % (x:real^3)) = &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let STDCAP_BALL_CHART = prove
 (`!P P'.
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\
     smooth_map_on (annulus (&1 / &4) (&2)) (\z:real^3. (P(norm z) / norm z) % z)
     ==> mfd_ball_chart euclidean (open_set_atlas (:real^3))
                        (stdcap_glue (P(&1 / &2) / &2) P) /\
         (!z. z IN annulus (&2 / &3) (&2)
              ==> stdcap_glue (P(&1 / &2) / &2) P z = (P(norm z) / norm z) % z) /\
         IMAGE (stdcap_glue (P(&1 / &2) / &2) P) (ball(vec 0,&1)) = ball(vec 0,P(&1)) /\
         IMAGE (stdcap_glue (P(&1 / &2) / &2) P) (cball(vec 0,&1)) = cball(vec 0,P(&1)) /\
         IMAGE (stdcap_glue (P(&1 / &2) / &2) P) (sphere(vec 0,&1)) = sphere(vec 0,P(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_GLUE_IMAGE_BALL) THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_GLUE_IMAGE_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC STDCAP_GLUE_BIG THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[mfd_ball_chart; mfd_param; MFD_DIFFEO_EUCLIDEAN] THEN
  MATCH_MP_TAC SCHI_INJ_DIFFEO THEN REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC STDCAP_GLUE_SMOOTH THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STDCAP_GLUE_INJ THEN
    MAP_EVERY EXISTS_TAC [`P:real->real`; `P':real->real`] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`P:real->real`; `P':real->real`; `x:real^3`] STDCAP_GLUE_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^3->real^3` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    MATCH_MP_TAC STDCAP_DET_NZ THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Metric bounds from quadratic form bounds m |v|^2 <= g(v,v)                *)
(* <= M |v|^2 on a ball of R^3: segments are short, so intrinsic distances   *)
(* in a ball and distances are at most sqrt M times Euclidean ones, metric   *)
(* balls contain Euclidean balls of radius r/sqrt M, and volumes lie between *)
(* m^(3/2) and M^(3/2) times the flat ones.                                  *)
(* ------------------------------------------------------------------------- *)

let STDCAP_FLAT_METRIC = prove
 (`metric_field (:real^3) (\x. mat 1) /\
   riemannian_metric (open_set_atlas (:real^3)) (\x:real^3. mat 1)`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[metric_field; OPEN_UNIV; IN_UNIV; TRANSP_MAT; MATRIX_VECTOR_MUL_LID] THEN
    REWRITE_TAC[o_DEF; SMOOTH_MAP_ON_CONST] THEN SIMP_TAC[DOT_POS_LT];
    SIMP_TAC[RFB_OPEN_SET_RIEMANNIAN; OPEN_UNIV]]);;

let STDCAP_OSA_FACTS = prove
 (`smooth_manifold_atlas euclidean (open_set_atlas (:real^3)) /\
   ((:real^3),(\x:real^3. x)) IN open_set_atlas (:real^3) /\
   (!g:real^3->real^3^3 y. metric_local (open_set_atlas (:real^3)) ((:real^3),(\x. x)) g y =
                           g y) /\
   (!y:real^3. chart_inv ((:real^3),(\x. x)) y = y)`,
  REWRITE_TAC[MFD_EUCLIDEAN_ATLAS; open_set_atlas; IN_SING] THEN
  SIMP_TAC[GSYM open_set_atlas; RFB_OPEN_SET_METRIC_LOCAL; OPEN_UNIV; IN_UNIV;
           MFDM_CHART_INV_ID]);;

let STDCAP_SEGMENT = prove
 (`!(g:real^3->real^3^3) m M rho y1 y2.
     riemannian_metric (open_set_atlas (:real^3)) g /\ &0 <= m /\
     (!y v. y IN ball(vec 0,rho)
            ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
     y1 IN ball(vec 0,rho) /\ y2 IN ball(vec 0,rho)
     ==> mfd_c1_curve (euclidean,open_set_atlas (:real^3)) (\t. y1 + t % (y2 - y1)) (&0) (&1) /\
         (!t. t IN real_interval[&0,&1] ==> y1 + t % (y2 - y1) IN ball(vec 0,rho)) /\
         mfd_length (open_set_atlas (:real^3)) g (\t. y1 + t % (y2 - y1)) (&0) (&1)
         <= sqrt M * dist(y1,y2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[y1:real^3,y2] SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_BALL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `(:real^3)`;
                 `\x:real^3. x`; `y1:real^3`; `y2:real^3`] GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[STDCAP_OSA_FACTS; IMAGE_ID; SUBSET_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[STDCAP_OSA_FACTS; ETA_AX] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `g:real^3->real^3^3`;
                 `(:real^3)`; `\x:real^3. x`; `y1:real^3`; `y2:real^3`; `m:real`; `M:real`;
                 `ball(vec 0:real^3,rho)`] GRGD_SEGMENT_LENGTH_UPPER) THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS; IMAGE_ID; SUBSET_UNIV; NORM_POW_2; ETA_AX] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
    concl th = `segment[y1:real^3,y2] SUBSET ball(vec 0,rho)`)) THEN
  REWRITE_TAC[segment; IN_ELIM_THM] THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let STDCAP_DIST_IN_BOUND = prove
 (`!(g:real^3->real^3^3) m M rho y1 y2.
     riemannian_metric (open_set_atlas (:real^3)) g /\ &0 <= m /\
     (!y v. y IN ball(vec 0,rho)
            ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
     y1 IN ball(vec 0,rho) /\ y2 IN ball(vec 0,rho)
     ==> mfd_dist_in (euclidean,open_set_atlas (:real^3)) g (ball(vec 0,rho)) y1 y2
         <= sqrt M * dist(y1,y2) /\
         mfd_joinable (euclidean,open_set_atlas (:real^3)) y1 y2 /\
         mfd_dist (euclidean,open_set_atlas (:real^3)) g y1 y2 <= sqrt M * dist(y1,y2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STDCAP_SEGMENT) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> not(is_forall(concl th)))) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g:real^3->real^3^3`; `ball(vec 0:real^3,rho)`;
                   `\t. (y1:real^3) + t % (y2 - y1)`; `&0`; `&1`] MFD_DIST_IN_LE_LENGTH) THEN
    ASM_REWRITE_TAC[STDCAP_OSA_FACTS] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                VECTOR_ARITH `y1 + (y2 - y1):real^3 = y2`] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[mfd_joinable] THEN EXISTS_TAC `\t. (y1:real^3) + t % (y2 - y1)` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g:real^3->real^3^3`;
                   `\t. (y1:real^3) + t % (y2 - y1)`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
    ASM_REWRITE_TAC[STDCAP_OSA_FACTS] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
                VECTOR_ARITH `y1 + (y2 - y1):real^3 = y2`] THEN
    ASM_REAL_ARITH_TAC]);;

let STDCAP_EBALL_IN_MBALL = prove
 (`!(g:real^3->real^3^3) m M rho y r.
     riemannian_metric (open_set_atlas (:real^3)) g /\ &0 <= m /\ &0 < M /\ &0 < r /\
     (!y v. y IN ball(vec 0,rho)
            ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
     ball(y,r / sqrt M) SUBSET ball(vec 0,rho)
     ==> ball(y,r / sqrt M) SUBSET mfd_ball (euclidean,open_set_atlas (:real^3)) g y r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt M` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN ball(vec 0,rho) /\ (w:real^3) IN ball(vec 0,rho)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_SIMP_TAC[REAL_LT_DIV];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3^3`; `m:real`; `M:real`; `rho:real`; `y:real^3`; `w:real^3`]
               STDCAP_DIST_IN_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sqrt M * dist(y:real^3,w)` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(w:real^3) IN ball(y,r / sqrt M)` THEN REWRITE_TAC[IN_BALL] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC);;

let STDCAP_FLAT_BALL_VOLUME = prove
 (`!(y:real^3) r. &0 <= r
       ==> mfd_has_volume (euclidean,open_set_atlas (:real^3)) (\x. mat 1)
                          (ball(y,r)) (&4 / &3 * pi * r pow 3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[open_set_atlas] THEN
  MP_TAC(ISPECL [`(:real^3)`; `ball(y:real^3,r)`; `&4 / &3 * pi * r pow 3`]
                MFD_HAS_VOLUME_EUCLIDEAN) THEN
  REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL; VOLUME_BALL]);;

let STDCAP_VOL_UPPER = prove
 (`!(g:real^3->real^3^3) m M rho S v w.
     riemannian_metric (open_set_atlas (:real^3)) g /\ &0 <= M /\
     (!y v. y IN ball(vec 0,rho)
            ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
     S SUBSET ball(vec 0,rho) /\
     mfd_has_volume (euclidean,open_set_atlas (:real^3)) g S v /\
     mfd_has_volume (euclidean,open_set_atlas (:real^3)) (\x. mat 1) S w
     ==> v <= M * sqrt M * w`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                        `g:real^3->real^3^3`; `\x:real^3. mat 1:real^3^3`; `S:real^3->bool`]
                       MFD_HAS_VOLUME_COMPARE_QF) THEN
  ASM_REWRITE_TAC[STDCAP_FLAT_METRIC; STDCAP_OSA_FACTS; MATRIX_VECTOR_MUL_LID] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `w':real^3`]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let STDCAP_VOL_LOWER = prove
 (`!(g:real^3->real^3^3) m M rho S v w.
     riemannian_metric (open_set_atlas (:real^3)) g /\ &0 < m /\
     (!y v. y IN ball(vec 0,rho)
            ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
     S SUBSET ball(vec 0,rho) /\
     mfd_has_volume (euclidean,open_set_atlas (:real^3)) g S v /\
     mfd_has_volume (euclidean,open_set_atlas (:real^3)) (\x. mat 1) S w
     ==> m * sqrt m * w <= v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `\x:real^3. mat 1:real^3^3`; `g:real^3->real^3^3`; `S:real^3->bool`;
                 `w:real`; `v:real`; `inv m`] MFD_HAS_VOLUME_COMPARE_QF) THEN
  ASM_REWRITE_TAC[STDCAP_FLAT_METRIC; STDCAP_OSA_FACTS; MATRIX_VECTOR_MUL_LID] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `u:real^3`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv m * (m * ((u:real^3) dot u))` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_LE_REFL];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt m` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `m * sqrt m * (inv m * sqrt(inv m) * v)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN ASM_SIMP_TAC[SQRT_INV] THEN
    UNDISCH_TAC `&0 < sqrt m` THEN UNDISCH_TAC `&0 < m` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The noncollapsing clause of the cap.  A metric ball B(y,r)               *)
(* with y in the core ball(0,rho1) and sup R = r^-2 on it either lies in the *)
(* core or meets its boundary sphere, the central sphere of the inner neck   *)
(* e'; then r <= sqrt 2 R(z')^(-1/2) and apx_eng_n2 keeps B(y,r) in the     *)
(* image of the compact slab abs(s) <= 3 of e'.  Its volume is at least that *)
(* of the Euclidean ball of radius r / sqrt M.                               *)
(* ------------------------------------------------------------------------- *)

(* A point of a metric ball outside a Euclidean ball centred at 0 that       *)
(* contains the centre: some point of the metric ball lies on the sphere.    *)

let STDCAP_BALL_CROSS = prove
 (`!(g:real^3->real^3^3) y r v rho.
     riemannian_metric (open_set_atlas (:real^3)) g /\ norm y < rho /\
     v IN mfd_ball (euclidean,open_set_atlas (:real^3)) g y r /\ rho <= norm v
     ==> ?w. w IN mfd_ball (euclidean,open_set_atlas (:real^3)) g y r /\ norm w = rho`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g:real^3->real^3^3`; `y:real^3`; `v:real^3`; `r:real`]
                APX_DIST_SHORT_CURVE) THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(\x. lift(norm(((gam:real->real^3) o drop) x))) continuous_on
                interval[lift(&0),lift(&1)]` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN; ETA_AX] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `gam:real->real^3`; `&0`; `&1`] GRGD_CURVE_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(norm(((gam:real->real^3) o drop) x))`; `lift(&0)`; `lift(&1)`;
                 `rho:real`; `1`] IVT_INCREASING_COMPONENT_ON_1) THEN
  ASM_REWRITE_TAC[LIFT_DROP; o_THM; DIMINDEX_1; LE_REFL; GSYM drop] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(gam:real->real^3)(drop s1)` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `s1 IN interval[lift(&0),lift(&1)]` THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g:real^3->real^3^3`; `gam:real->real^3`; `&0`; `drop s1`; `&1`]
                MFD_LENGTH_COMBINE) THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [UNDISCH_THEN `(gam:real->real^3)(&0) = y` (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MFD_C1_CURVE_JOINABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN `(gam:real->real^3)(&0) = y` (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `mfd_length (open_set_atlas (:real^3)) g (gam:real->real^3) (&0) (drop s1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_DIST_LE_LENGTH THEN ASM_REWRITE_TAC[STDCAP_OSA_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g:real^3->real^3^3`; `gam:real->real^3`; `drop s1`; `&1`]
                MFD_LENGTH_POS_LE) THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS] THEN ASM_REAL_ARITH_TAC);;

(* Closed slabs of the neck coordinates (copies of P2BN_SVAL_NORM and         *)
(* P2BN_CLOSED_SLAB, pc_p2b_neckbd, which lies above the interface files).    *)

let STDCAP_SVAL_NORM = prove
 (`!y:real^3 a.
     ~(y = vec 0)
     ==> (abs(apx_sval y) <= a <=>
          exp(--a / sqrt(&2)) <= norm y /\ norm y <= exp(a / sqrt(&2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3) /\ &0 < sqrt(&2)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NORM_POS_LT; SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  MP_TAC(SPECL [`--a / sqrt(&2)`; `log(norm(y:real^3))`] REAL_EXP_MONO_LE) THEN
  MP_TAC(SPECL [`log(norm(y:real^3))`; `a / sqrt(&2)`] REAL_EXP_MONO_LE) THEN
  ASM_SIMP_TAC[EXP_LOG] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let STDCAP_CLOSED_SLAB = prove
 (`!Lam. &0 <= Lam
         ==> compact {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} /\
             (!eps. Lam < inv eps
                    ==> {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} SUBSET
                        rfs_neck_dom eps)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= Lam} =
                {z | exp(--Lam / sqrt(&2)) <= norm z /\ norm z <= exp(Lam / sqrt(&2))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_SIMP_TAC[STDCAP_SVAL_NORM] THEN
    REWRITE_TAC[NORM_0] THEN MP_TAC(SPEC `--Lam / sqrt(&2)` REAL_EXP_POS_LT) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `{z:real^3 | exp(--Lam / sqrt(&2)) <= norm z /\ norm z <= exp(Lam / sqrt(&2))} =
                  cball(vec 0,exp(Lam / sqrt(&2))) DIFF ball(vec 0,exp(--Lam / sqrt(&2)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_CBALL; OPEN_BALL]];
    X_GEN_TAC `eps:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Lam / sqrt(&2) < inv(sqrt(&2) * eps)` ASSUME_TAC THENL
     [SUBGOAL_THEN `inv(sqrt(&2) * eps) = inv eps / sqrt(&2)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_INV_MUL; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV2_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; rfs_neck_dom; annulus] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `exp(--(inv(sqrt(&2) * eps))) < exp(--Lam / sqrt(&2)) /\
                  exp(Lam / sqrt(&2)) < exp(inv(sqrt(&2) * eps))` MP_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LT; real_div; REAL_MUL_LNEG; REAL_LT_NEG2] THEN
      ASM_REWRITE_TAC[GSYM real_div];
      ASM_REAL_ARITH_TAC]]);;

(* The radius bound: with R >= cR > 0 at the centre, sup R = r^-2 forces     *)
(* r <= cR^(-1/2), and R <= r^-2 on the ball.                                *)

let STDCAP_SUP_RADIUS = prove
 (`!(g:real^3->real^3^3) y r cR.
     riemannian_metric (open_set_atlas (:real^3)) g /\ &0 < cR /\ &0 < r /\
     cR <= mfd_scalar (open_set_atlas (:real^3)) g y /\
     (?B. !w. w IN mfd_ball (euclidean,open_set_atlas (:real^3)) g y r
              ==> mfd_scalar (open_set_atlas (:real^3)) g w <= B) /\
     sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) g)
               (mfd_ball (euclidean,open_set_atlas (:real^3)) g y r)) = inv(r pow 2)
     ==> (!w. w IN mfd_ball (euclidean,open_set_atlas (:real^3)) g y r
              ==> mfd_scalar (open_set_atlas (:real^3)) g w <= inv(r pow 2)) /\
         r <= inv(sqrt cR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. w IN mfd_ball (euclidean,open_set_atlas (:real^3)) g y r
                    ==> mfd_scalar (open_set_atlas (:real^3)) g w <= inv(r pow 2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "sup")) (concl th))) THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `mfd_scalar (open_set_atlas (:real^3)) g w`] THEN
    REWRITE_TAC[REAL_LE_REFL; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cR <= inv(r pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_scalar (open_set_atlas (:real^3)) g y` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g:real^3->real^3^3`; `y:real^3`; `r:real`] MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[STDCAP_OSA_FACTS; TOPSPACE_EUCLIDEAN; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `r pow 2 <= inv cR` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`cR:real`; `inv(r pow 2)`] REAL_LE_INV2) THEN
    ASM_REWRITE_TAC[REAL_INV_INV];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SQRT_INV] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REWRITE_TAC[]);;

let STDCAP_SQRT2_LE = prove
 (`sqrt(&2) <= &71 / &50`,
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Balls B(y,r) with y in the core and R <= r^-2 on the ball have compact    *)
(* closure inside U.                                                          *)

let STDCAP_NONCOLL_BALL = prove
 (`!(g:real^3->real^3^3) eps z' e' rho1 rho2 y r.
     riemannian_metric (open_set_atlas (:real^3)) g /\
     apx_ch_ctx euclidean (open_set_atlas (:real^3)) g eps /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z' e' /\
     IMAGE e' (sphere(vec 0,&1)) = sphere(vec 0,rho1) /\
     IMAGE e' (rfs_neck_dom eps) SUBSET ball(vec 0,rho2) /\ rho1 < rho2 /\
     y IN ball(vec 0,rho1) /\ &0 < r /\
     (!w. w IN mfd_ball (euclidean,open_set_atlas (:real^3)) g y r
          ==> mfd_scalar (open_set_atlas (:real^3)) g w <= inv(r pow 2))
     ==> compact_in euclidean
           (euclidean closure_of mfd_ball (euclidean,open_set_atlas (:real^3)) g y r) /\
         euclidean closure_of mfd_ball (euclidean,open_set_atlas (:real^3)) g y r
         SUBSET ball(vec 0,rho2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [apx_ch_ctx]) THEN
  SUBGOAL_THEN `&0 < inv eps /\ &1024 <= inv eps` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    SUBGOAL_THEN `inv(&1 / &1024) <= inv eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EUCLIDEAN_CLOSURE_OF; COMPACT_IN_EUCLIDEAN] THEN
  ABBREV_TAC `S = mfd_ball (euclidean,open_set_atlas (:real^3)) g y r` THEN
  ASM_CASES_TAC `(S:real^3->bool) SUBSET ball(vec 0,rho1)` THENL
   [SUBGOAL_THEN `closure(S:real^3->bool) SUBSET cball(vec 0,rho1)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CBALL] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^3,rho1)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_CLOSURE] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,rho1)` THEN ASM_REWRITE_TAC[BOUNDED_BALL];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(vec 0:real^3,rho1)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_BALL_0;
                                      REAL_NOT_LT] o check (fun th -> is_neg(concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`g:real^3->real^3^3`; `y:real^3`; `r:real`; `v:real^3`; `rho1:real`]
               STDCAP_BALL_CROSS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_BALL_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y1. y1 IN sphere(vec 0,&1) /\ (e':real^3->real^3) y1 = w`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e':real^3->real^3) (sphere(vec 0,&1)) = sphere(vec 0,rho1)` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
    ASM_REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y1:real^3) IN rfs_neck_dom eps /\ apx_sval y1 = &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[APX_UNIT_SPHERE_NECK_DOM; SUBSET];
      MATCH_MP_TAC APX_SVAL_UNIT THEN ASM_MESON_TAC[IN_SPHERE_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mfd_scalar (open_set_atlas (:real^3)) g z'` ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  ABBREV_TAC `h = inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) g z'))` THEN
  SUBGOAL_THEN `&0 < h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC REAL_LT_INV THEN ASM_SIMP_TAC[SQRT_POS_LT];
    ALL_TAC] THEN
  (* r <= sqrt 2 h, since R(z') <= 2 R(w) <= 2 r^-2 *)
  SUBGOAL_THEN `r <= sqrt(&2) * h` ASSUME_TAC THENL
   [SUBGOAL_THEN `mfd_scalar (open_set_atlas (:real^3)) g z' <= &2 * inv(r pow 2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * mfd_scalar (open_set_atlas (:real^3)) g w` THEN CONJ_TAC THENL
       [UNDISCH_THEN `(e':real^3->real^3) y1 = w` (SUBST1_TAC o SYM) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `&2`)) (concl th) &&
          not(can (find_term (fun t -> t = `&3 / &2`)) (concl th)))) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "h" THEN
    SUBGOAL_THEN `sqrt(&2) * inv(sqrt(mfd_scalar (open_set_atlas (:real^3)) g z')) =
                  sqrt(&2 / mfd_scalar (open_set_atlas (:real^3)) g z')` SUBST1_TAC THENL
     [REWRITE_TAC[SQRT_DIV; real_div]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    UNDISCH_TAC `mfd_scalar (open_set_atlas (:real^3)) g z' <= &2 * inv(r pow 2)` THEN
    SUBGOAL_THEN `&0 < r pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * inv(r pow 2)) * r pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; GSYM REAL_MUL_ASSOC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* S lies in the image of the closed slab abs(s) <= 3 of e' *)
  SUBGOAL_THEN `(S:real^3->bool) SUBSET
                IMAGE (e':real^3->real^3) {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= &3}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_joinable (euclidean,open_set_atlas (:real^3)) w u /\
                  mfd_dist (euclidean,open_set_atlas (:real^3)) g w u < &2 * r`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN S` THEN UNDISCH_TAC `(u:real^3) IN S` THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[MFD_JOINABLE_SYM; MFD_JOINABLE_TRANS; STDCAP_OSA_FACTS];
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `mfd_dist (euclidean,open_set_atlas (:real^3)) g w y +
                    mfd_dist (euclidean,open_set_atlas (:real^3)) g y u` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MFD_DIST_TRIANGLE THEN
          ASM_MESON_TAC[MFD_JOINABLE_SYM; STDCAP_OSA_FACTS];
          MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                         `g:real^3->real^3^3`; `w:real^3`; `y:real^3`] MFD_DIST_SYM) THEN
          REWRITE_TAC[STDCAP_OSA_FACTS] THEN DISCH_THEN SUBST1_TAC THEN
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC STDCAP_SQRT2_LE THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 * r <= &71 / &25 * h` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * sqrt(&2) * h` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g:real^3->real^3^3`; `eps:real`; `z':real^3`; `e':real^3->real^3`;
                   `y1:real^3`; `u:real^3`] APX_NECK_EXIT_BALL) THEN
    ASM_REWRITE_TAC[STDCAP_OSA_FACTS; REAL_ABS_NUM; REAL_SUB_RZERO] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&71 / &25 * h` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&71 / &25 * h <= (&99 / &100 * inv eps) * h` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z1:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    EXISTS_TAC `z1:real^3` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPECL [`eps:real`; `z1:real^3`] APX_SVAL_NECK_DOM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z':real^3`; `e':real^3->real^3`; `y1:real^3`; `z1:real^3`] o
      REWRITE_RULE[apx_eng_n2] o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "apx_eng_n2")) (concl th) &&
        can (find_term (fun t -> t = `&1 / &100`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_ABS_NEG; REAL_ABS_NUM; REAL_SUB_RZERO] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&99 / &100 * min (abs(apx_sval z1)) (&2 * inv eps - abs(apx_sval z1))) * h <
                  (&71 / &25) * h`
    MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* compactness of the slab image *)
  MP_TAC(SPEC `&3` STDCAP_CLOSED_SLAB) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `eps:real`)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (e':real^3->real^3)
                         {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= &3})` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z' e'` THEN
    REWRITE_TAC[rfs_neck] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_CLOSURE] THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (e':real^3->real^3)
                  {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= &3}` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (e':real^3->real^3)
                  {z:real^3 | ~(z = vec 0) /\ abs(apx_sval z) <= &3}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (e':real^3->real^3) (rfs_neck_dom eps)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]]);;

(* The volume bound of the noncollapsing clause.                              *)

let STDCAP_NONCOLL_VOL = prove
 (`!(g:real^3->real^3^3) m M cR rho1 rho3 y r.
     riemannian_metric (open_set_atlas (:real^3)) g /\
     &0 < m /\ &1 <= M /\ &0 < cR /\ rho1 + inv(sqrt cR) <= rho3 /\
     (!y v. y IN ball(vec 0,rho3)
            ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
     y IN ball(vec 0,rho1) /\ &0 < r /\ r <= inv(sqrt cR) /\
     compact_in euclidean
       (euclidean closure_of mfd_ball (euclidean,open_set_atlas (:real^3)) g y r)
     ==> ?v. mfd_has_volume (euclidean,open_set_atlas (:real^3)) g
                            (mfd_ball (euclidean,open_set_atlas (:real^3)) g y r) v /\
             m * sqrt m * (&4 / &3 * pi) / (M * sqrt M) <= v / r pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = mfd_ball (euclidean,open_set_atlas (:real^3)) g y r` THEN
  SUBGOAL_THEN `open_in euclidean (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[STDCAP_OSA_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g:real^3->real^3^3`; `euclidean closure_of (S:real^3->bool)`]
                MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[STDCAP_OSA_FACTS; HAUSDORFF_SPACE_EUCLIDEAN] THEN
  DISCH_THEN(X_CHOOSE_TAC `wc:real`) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g:real^3->real^3^3`; `S:real^3->bool`; `euclidean closure_of (S:real^3->bool)`;
                 `wc:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[STDCAP_OSA_FACTS; MFD_LEBESGUE_MEASURABLE_OPEN] THEN
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    STRIP_TAC] THEN
  EXISTS_TAC `mfd_volume (euclidean,open_set_atlas (:real^3)) g (S:real^3->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < M /\ &1 <= sqrt M /\ &0 < sqrt M /\ sqrt M pow 2 = M`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `E = ball(y:real^3,r / sqrt M)` THEN
  SUBGOAL_THEN `(E:real^3->bool) SUBSET ball(vec 0,rho3)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_BALL_0] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `r / sqrt M <= r` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `r * &1 <= r * sqrt M` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN ball(vec 0,rho1)` THEN REWRITE_TAC[IN_BALL_0] THEN
    MP_TAC(ISPECL [`x:real^3`; `y:real^3`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`y:real^3`; `x:real^3`] NORM_SUB) THEN
    UNDISCH_TAC `dist(y:real^3,x) < r / sqrt M` THEN REWRITE_TAC[dist] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->bool) SUBSET S` ASSUME_TAC THENL
   [MP_TAC(SPECL [`g:real^3->real^3^3`; `m:real`; `M:real`; `rho3:real`; `y:real^3`; `r:real`]
                 STDCAP_EBALL_IN_MBALL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `g:real^3->real^3^3`; `E:real^3->bool`; `S:real^3->bool`;
                 `mfd_volume (euclidean,open_set_atlas (:real^3)) g (S:real^3->bool)`]
                MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[STDCAP_OSA_FACTS] THEN MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_OPEN THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[STDCAP_OSA_FACTS; OPEN_IN_EUCLIDEAN; OPEN_BALL];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3^3`; `m:real`; `M:real`; `rho3:real`; `E:real^3->bool`;
                 `mfd_volume (euclidean,open_set_atlas (:real^3)) g (E:real^3->bool)`;
                 `&4 / &3 * pi * (r / sqrt M) pow 3`] STDCAP_VOL_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "E" THEN MATCH_MP_TAC STDCAP_FLAT_BALL_VOLUME THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < r pow 3` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `(m * sqrt m * (&4 / &3 * pi) / (M * sqrt M)) * r pow 3 =
                m * sqrt m * (&4 / &3 * pi * (r / sqrt M) pow 3)` SUBST1_TAC THENL
   [UNDISCH_TAC `sqrt M pow 2 = M` THEN UNDISCH_TAC `&0 < sqrt M` THEN
    SPEC_TAC(`sqrt M`,`s:real`) THEN GEN_TAC THEN CONV_TAC REAL_FIELD;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The cap.  For a metric g on R^3 with an outer eps-neck e                   *)
(* whose image is the annulus between radii P(1) and rho2, an inner eps-neck *)
(* e' seen through a sphere diffeomorphism f as the radial map               *)
(* P(|y|)/|y| y on annulus(1/4,2), and uniform bounds on g, R, grad R and   *)
(* Lap R + 2|Ric|^2, the ball ball(0,rho2) with core ball(0,P(1)) is a       *)
(* (C,eps)-cap, C = stdcap_const of the bounds.                              *)
(* ------------------------------------------------------------------------- *)

let stdcap_const = new_definition
 `stdcap_const (m:real) (M:real) (cR:real) (KR:real) (K1:real) (K2:real) (rho2:real) =
    &2 + &2 * rho2 * sqrt M * sqrt KR + KR / cR +
    M * sqrt M * (&4 / &3 * pi * rho2 pow 3) * KR * sqrt KR +
    (M * sqrt M) / (m * sqrt m * (&4 / &3 * pi)) +
    K1 / (cR * sqrt cR) + K2 / cR pow 2`;;

let STDCAP_RADIAL_EXT_NORM = prove
 (`!(f:real^3->real^3) f' y.
     sphere_diffeo f f' /\ ~(y = vec 0) ==> norm(radial_ext f y) = norm y`,
  REWRITE_TAC[sphere_diffeo; radial_ext; IN_SPHERE_0] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `norm((f:real^3->real^3)(inv(norm(y:real^3)) % y)) = &1`
  (fun th -> REWRITE_TAC[th; REAL_MUL_RID]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv(norm(y:real^3)) % y` o check (fun th ->
    is_forall(concl th))) THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0] THEN SIMP_TAC[]);;

let STDCAP_RADIAL_EXT_SPHERE = prove
 (`!(f:real^3->real^3) f'.
     sphere_diffeo f f' ==> IMAGE (radial_ext f) (sphere(vec 0,&1)) = sphere(vec 0,&1)`,
  REWRITE_TAC[sphere_diffeo] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN sphere(vec 0,&1) ==> radial_ext f y = f y` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; radial_ext] THEN SIMP_TAC[REAL_INV_1; VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
    DISCH_TAC THEN EXISTS_TAC `(f':real^3->real^3) x` THEN ASM_SIMP_TAC[]]);;

let STDCAP_NECK_DOM_ANNULUS = prove
 (`!eps. &0 < eps /\ eps <= &1 / &1024
         ==> annulus (&1 / &4) (&2) SUBSET rfs_neck_dom eps:real^3->bool`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_neck_dom; SUBSET; annulus; IN_ELIM_THM] THEN
  ABBREV_TAC `c = inv(sqrt(&2) * eps)` THEN
  SUBGOAL_THEN `&4 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    SUBGOAL_THEN `inv(&1 / &4) <= inv(sqrt(&2) * eps)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH];
        SUBGOAL_THEN `sqrt(&2) * eps <= &71 / &50 * (&1 / &1024)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN
          ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS; REAL_LT_IMP_LE; STDCAP_SQRT2_LE];
          REAL_ARITH_TAC]];
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 < exp c` ASSUME_TAC THENL
   [MP_TAC(SPEC `c:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(--c) < &1 / &4` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBGOAL_THEN `inv(exp c) < inv(&4)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN ASM_REAL_ARITH_TAC);;

let STDCAP_E_SMOOTH = prove
 (`!(g:real^3->real^3^3) eps z' e' f f' (P:real->real).
     rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z' e' /\ &0 < eps /\
     eps <= &1 / &1024 /\ sphere_diffeo f f' /\
     (!y. y IN annulus (&1 / &4) (&2) ==> e'(radial_ext f y) = (P(norm y) / norm y) % y)
     ==> smooth_map_on (annulus (&1 / &4) (&2)) (\z:real^3. (P(norm z) / norm z) % z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(e':real^3->real^3) o radial_ext f` THEN
  REWRITE_TAC[OPEN_ANNULUS; o_THM] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1 / &4) (&2) ==> ~(y = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `&1 / &4 < norm(y:real^3)` THEN ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `rfs_neck_dom eps:real^3->bool` THEN REWRITE_TAC[OPEN_ANNULUS] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[rfs_neck_dom; OPEN_ANNULUS];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `eps:real` STDCAP_NECK_DOM_ANNULUS) THEN ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(SPECL [`f:real^3->real^3`; `f':real^3->real^3`; `y:real^3`]
                 STDCAP_RADIAL_EXT_NORM) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN annulus (&1 / &4) (&2)` THEN
    ASM_REWRITE_TAC[annulus; IN_ELIM_THM];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `{x:real^3 | ~(x = vec 0)}` THEN
    CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_RADIAL_EXT THEN ASM_MESON_TAC[sphere_diffeo];
    UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z' e'` THEN
    REWRITE_TAC[rfs_neck; mfd_param; MFD_DIFFEO_EUCLIDEAN; diffeomorphism_on] THEN
    MESON_TAC[]]);;

let STDCAP_SUP_BOUNDS = prove
 (`!(g:real^3->real^3^3) U cR KR.
     ~(U = {}) /\
     (!y. y IN U ==> cR <= mfd_scalar (open_set_atlas (:real^3)) g y /\
                     mfd_scalar (open_set_atlas (:real^3)) g y <= KR)
     ==> cR <= sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) g) U) /\
         sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) g) U) <= KR`,
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `y0:real^3` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    MAP_EVERY EXISTS_TAC [`KR:real`; `mfd_scalar (open_set_atlas (:real^3)) g y0`] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; FORALL_IN_IMAGE];
    MATCH_MP_TAC REAL_SUP_LE THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[]]);;

let STDCAP_DIV_LE = prove
 (`!x y K c. &0 <= x /\ x <= K /\ &0 < c /\ c <= y ==> x / y <= K / c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x / c` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ]]);;

let STDCAP_DIV_LE2 = prove
 (`!x y K c. x <= K /\ &0 <= K /\ &0 < c /\ c <= y ==> x / y <= K / c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= x` THENL
   [MATCH_MP_TAC STDCAP_DIV_LE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= --a ==> a <= &0`) THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]]);;

(* The charts of the ball case of rfs_cap.                                    *)

let STDCAP_BALL_CASE = prove
 (`!(g:real^3->real^3^3) eps P P' z e z' e' f f' rho2.
     &0 < eps /\ eps <= &1 / &1024 /\
     (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
     &0 < P(&1 / &2) /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z e /\
     IMAGE e (rfs_neck_dom eps) = annulus (P(&1)) rho2 /\
     rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z' e' /\
     IMAGE e' (rfs_neck_dom eps) SUBSET ball(vec 0,rho2) /\
     sphere_diffeo f f' /\
     (!y. y IN annulus (&1 / &4) (&2) ==> e'(radial_ext f y) = (P(norm y) / norm y) % y)
     ==> &0 < P(&1) /\ P(&1) < rho2 /\
         IMAGE e' (sphere(vec 0,&1)) = sphere(vec 0,P(&1)) /\
         ?b. mfd_ball_chart euclidean (open_set_atlas (:real^3)) b /\
             IMAGE b (ball(vec 0,&2)) SUBSET ball(vec 0,rho2) /\
             ball(vec 0,P(&1)) = IMAGE b (ball(vec 0,&1)) /\
             IMAGE e (rfs_neck_dom eps) = ball(vec 0,rho2) DIFF IMAGE b (cball(vec 0,&1)) /\
             IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
             (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`g:real^3->real^3^3`; `eps:real`; `z':real^3`; `e':real^3->real^3`;
                `f:real^3->real^3`; `f':real^3->real^3`; `P:real->real`] STDCAP_E_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_BALL_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b = stdcap_glue (P(&1 / &2) / &2) P` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`P:real->real`; `P':real->real`] STDCAP_P_ONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y:real^3. y IN annulus (&1) (&2)
                         ==> (b:real^3->real^3) y = (e':real^3->real^3)(radial_ext f y)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN annulus (&2 / &3) (&2) /\ y IN annulus (&1 / &4) (&2)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (e':real^3->real^3) (sphere(vec 0,&1)) = sphere(vec 0,P(&1))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`f:real^3->real^3`; `f':real^3->real^3`] STDCAP_RADIAL_EXT_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (b:real^3->real^3) (sphere(vec 0,&1)) = sphere(vec 0,P(&1))`)) THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (F1:real^3->real^3) x = F2 x)
                           ==> IMAGE F1 s = IMAGE F2 s`) THEN
    REWRITE_TAC[IN_SPHERE_0; o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&2 / &3) (&2) /\ x IN annulus (&1 / &4) (&2)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P(&1) < rho2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^3) IN annulus (P(&1)) rho2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (e:real^3->real^3) (rfs_neck_dom eps) = annulus (P(&1)) rho2`)) THEN
      UNDISCH_TAC `rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z e` THEN
      REWRITE_TAC[rfs_neck] THEN STRIP_TAC THEN
      MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `b:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN ASM_CASES_TAC `norm(y:real^3) <= &1` THENL
     [SUBGOAL_THEN `(b:real^3->real^3) y IN cball(vec 0,P(&1))` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `IMAGE (b:real^3->real^3) (cball(vec 0,&1)) = cball(vec 0,P(&1))`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
        REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `(y:real^3) IN annulus (&1) (&2)` ASSUME_TAC THENL
       [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(e':real^3->real^3)(radial_ext f y) IN ball(vec 0,rho2)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `IMAGE (e':real^3->real^3) (rfs_neck_dom eps) SUBSET ball(vec 0,rho2)`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        MP_TAC(SPEC `eps:real` STDCAP_NECK_DOM_ANNULUS) THEN ASM_REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        MP_TAC(SPECL [`f:real^3->real^3`; `f':real^3->real^3`; `y:real^3`]
                     STDCAP_RADIAL_EXT_NORM) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(y:real^3) IN annulus (&1) (&2)` THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[IN_BALL_0]]];
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; annulus; IN_ELIM_THM] THEN
    REAL_ARITH_TAC]);;

(* The cap theorem.                                                           *)

let STDCAP_CAP = prove
 (`?epsc. &0 < epsc /\
     !(g:real^3->real^3^3) eps P P' z e z' e' f f' rho2 rho3 m M cR KR K1 K2.
       riemannian_metric (open_set_atlas (:real^3)) g /\ &0 < eps /\ eps <= epsc /\
       (!r. &1 / &4 < r /\ r < &2 ==> (P has_real_derivative P' r) (atreal r) /\ &0 < P' r) /\
       &0 < P(&1 / &2) /\
       rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z e /\
       IMAGE e (rfs_neck_dom eps) = annulus (P(&1)) rho2 /\
       rfs_neck (euclidean,open_set_atlas (:real^3)) g eps z' e' /\
       IMAGE e' (rfs_neck_dom eps) SUBSET ball(vec 0,rho2) /\
       sphere_diffeo f f' /\
       (!y. y IN annulus (&1 / &4) (&2) ==> e'(radial_ext f y) = (P(norm y) / norm y) % y) /\
       &0 < m /\ &1 <= M /\ &0 < cR /\ &0 <= K1 /\ &0 <= K2 /\ rho2 + inv(sqrt cR) <= rho3 /\
       (!y v. y IN ball(vec 0,rho3)
              ==> m * (v dot v) <= v dot (g y ** v) /\ v dot (g y ** v) <= M * (v dot v)) /\
       (!y. y IN ball(vec 0,rho3)
            ==> cR <= mfd_scalar (open_set_atlas (:real^3)) g y /\
                mfd_scalar (open_set_atlas (:real^3)) g y <= KR) /\
       (!y. y IN ball(vec 0,rho2)
            ==> sqrt(rfs_scalar_grad2 (open_set_atlas (:real^3)) g y) <= K1 /\
                abs(rfs_scalar_lap (open_set_atlas (:real^3)) g y +
                    &2 * rfs_ric_norm2 (open_set_atlas (:real^3)) g y) <= K2)
       ==> rfs_cap (euclidean,open_set_atlas (:real^3)) g (stdcap_const m M cR KR K1 K2 rho2)
                   eps (ball(vec 0,rho2)) (ball(vec 0,P(&1)))`,
  MP_TAC(INST_TYPE [`:real^3`,`:A`] APX_CH_CTX_HOLDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `eps0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctx"))) THEN
  EXISTS_TAC `min eps0 (&1 / &1024)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `apx_ch_ctx euclidean (open_set_atlas (:real^3)) (g:real^3->real^3^3) eps`
  ASSUME_TAC THENL
   [USE_THEN "ctx" (MP_TAC o SPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                                    `g:real^3->real^3^3`; `eps:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; STDCAP_OSA_FACTS] THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps <= &1 / &1024` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3^3`; `eps:real`; `P:real->real`; `P':real->real`;
                `z:real^3`; `e:real^3->real^3`; `z':real^3`; `e':real^3->real^3`;
                `f:real^3->real^3`; `f':real^3->real^3`; `rho2:real`] STDCAP_BALL_CASE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `b:real^3->real^3` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `ball(vec 0,P(&1)) = IMAGE (b:real^3->real^3) (ball(vec 0,&1))`)) THEN
  (* basic numerical facts *)
  SUBGOAL_THEN `&0 < rho2 /\ cR <= KR /\ &0 < KR` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ (b ==> c) ==> a /\ b /\ c`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[CENTRE_IN_BALL] THEN
        SUBGOAL_THEN `&0 <= inv(sqrt cR)` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
          ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,rho2) SUBSET ball(vec 0,rho3)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    SUBGOAL_THEN `&0 <= inv(sqrt cR)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt M /\ &0 < sqrt m /\ &0 < sqrt cR /\ &0 < sqrt KR`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `CC = stdcap_const m M cR KR K1 K2 rho2` THEN
  ABBREV_TAC `sp = sup(IMAGE (mfd_scalar (open_set_atlas (:real^3)) g) (ball(vec 0:real^3,rho2)))` THEN
  SUBGOAL_THEN `cR <= sp /\ sp <= KR` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "sp" THEN MATCH_MP_TAC STDCAP_SUP_BOUNDS THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `vec 0:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sp /\ &0 < sqrt sp /\ inv(sqrt KR) <= inv(sqrt sp)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ (b ==> c) ==> a /\ b /\ c`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the six constant clauses: the terms of CC *)
  SUBGOAL_THEN
   `&0 <= &2 * rho2 * sqrt M * sqrt KR /\ &0 <= KR / cR /\
    &0 <= M * sqrt M * (&4 / &3 * pi * rho2 pow 3) * KR * sqrt KR /\
    &0 <= (M * sqrt M) / (m * sqrt m * (&4 / &3 * pi)) /\
    &0 <= K1 / (cR * sqrt cR) /\ &0 <= K2 / cR pow 2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < pi` ASSUME_TAC THENL [REWRITE_TAC[PI_POS]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_DIV) THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < CC /\ &2 * rho2 * sqrt M * sqrt KR < CC /\ KR / cR < CC /\
                M * sqrt M * (&4 / &3 * pi * rho2 pow 3) * KR * sqrt KR < CC /\
                (M * sqrt M) / (m * sqrt m * (&4 / &3 * pi)) < CC /\
                K1 / (cR * sqrt cR) < CC /\ K2 / cR pow 2 < CC` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "CC" THEN REWRITE_TAC[stdcap_const] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[rfs_cap] THEN ASM_REWRITE_TAC[STDCAP_OSA_FACTS; OPEN_IN_EUCLIDEAN; OPEN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [(* ball case *)
    DISJ1_TAC THEN MAP_EVERY EXISTS_TAC
     [`b:real^3->real^3`; `e:real^3->real^3`; `e':real^3->real^3`; `z:real^3`; `z':real^3`;
      `f:real^3->real^3`; `f':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* R > 0 *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `cR:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    (* diameter *)
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `&2 * rho2 * sqrt M` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `CC * inv(sqrt KR)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `d:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`g:real^3->real^3^3`; `m:real`; `M:real`; `rho2:real`; `y1:real^3`;
                    `y2:real^3`] STDCAP_DIST_IN_BOUND) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `v:real^3`] o check (fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = `M:real`)) (concl th))) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      SUBGOAL_THEN `dist(y1:real^3,y2) <= &2 * rho2` MP_TAC THENL
       [UNDISCH_TAC `(y1:real^3) IN ball(vec 0,rho2)` THEN
        UNDISCH_TAC `(y2:real^3) IN ball(vec 0,rho2)` THEN
        REWRITE_TAC[IN_BALL_0; dist] THEN NORM_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `sqrt M * dist(y1:real^3,y2) <= sqrt M * (&2 * rho2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; REAL_ARITH_TAC]];
    (* ratio *)
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `KR / cR` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `y1:real^3` (X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC STDCAP_DIV_LE2 THEN
    FIRST_ASSUM(MP_TAC o SPEC `y1:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y2:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN ASM_REAL_ARITH_TAC;
    (* volume *)
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g:real^3->real^3^3`; `cball(vec 0:real^3,rho2)`] MFD_HAS_VOLUME_COMPACT) THEN
    ASM_REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEAN; STDCAP_OSA_FACTS; COMPACT_IN_EUCLIDEAN;
                    COMPACT_CBALL] THEN
    DISCH_THEN(X_CHOOSE_TAC `wc:real`) THEN
    MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `g:real^3->real^3^3`; `ball(vec 0:real^3,rho2)`; `cball(vec 0:real^3,rho2)`;
                   `wc:real`] MFD_HAS_VOLUME_SUBSET) THEN
    ASM_SIMP_TAC[STDCAP_OSA_FACTS; MFD_LEBESGUE_MEASURABLE_OPEN; OPEN_IN_EUCLIDEAN; OPEN_BALL;
                 BALL_SUBSET_CBALL] THEN
    STRIP_TAC THEN
    EXISTS_TAC `mfd_volume (euclidean,open_set_atlas (:real^3)) g (ball(vec 0:real^3,rho2))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`g:real^3->real^3^3`; `m:real`; `M:real`; `rho3:real`;
                  `ball(vec 0:real^3,rho2)`;
                  `mfd_volume (euclidean,open_set_atlas (:real^3)) g (ball(vec 0:real^3,rho2))`;
                  `&4 / &3 * pi * rho2 pow 3`] STDCAP_VOL_UPPER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC STDCAP_FLAT_BALL_VOLUME THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `M * sqrt M * &4 / &3 * pi * rho2 pow 3` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(sqrt sp pow 3) >= inv(KR * sqrt KR)` MP_TAC THENL
     [REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `KR * sqrt KR = sqrt KR pow 3` SUBST1_TAC THENL
         [SUBGOAL_THEN `sqrt KR pow 2 = KR` MP_TAC THENL
           [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_RING];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[real_ge] THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `CC * inv(KR * sqrt KR)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < KR * sqrt KR` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    (* noncollapsing *)
    EXISTS_TAC `m * sqrt m * (&4 / &3 * pi) / (M * sqrt M)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `&0 < m * sqrt m * (&4 / &3 * pi) / (M * sqrt M)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
        CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `&1 <= M` THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(m * sqrt m * (&4 / &3 * pi) / (M * sqrt M)) =
                    (M * sqrt M) / (m * sqrt m * (&4 / &3 * pi))` ASSUME_TAC THENL
       [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      MATCH_MP_TAC REAL_LT_INV2 THEN ASM_SIMP_TAC[REAL_LT_INV];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `r:real`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`g:real^3->real^3^3`; `y:real^3`; `r:real`; `cR:real`] STDCAP_SUP_RADIUS) THEN
    SUBGOAL_THEN `(y:real^3) IN ball(vec 0,rho3)` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN ball(vec 0,P(&1))` THEN
      UNDISCH_TAC `ball(vec 0:real^3,rho2) SUBSET ball(vec 0,rho3)` THEN
      UNDISCH_TAC `P(&1) < rho2` THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN
      MESON_TAC[REAL_LT_TRANS];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
          is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
        ASM_SIMP_TAC[];
        EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[]];
      STRIP_TAC] THEN
    MP_TAC(SPECL [`g:real^3->real^3^3`; `eps:real`; `z':real^3`; `e':real^3->real^3`;
                  `P(&1):real`; `rho2:real`; `y:real^3`; `r:real`] STDCAP_NONCOLL_BALL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STDCAP_NONCOLL_VOL THEN
    MAP_EVERY EXISTS_TAC [`cR:real`; `P(&1):real`; `rho3:real`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rho2 + inv(sqrt cR) <= rho3` THEN UNDISCH_TAC `P(&1) < rho2` THEN
    REAL_ARITH_TAC;
    (* gradient *)
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `K1 / (cR * sqrt cR)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STDCAP_DIV_LE2 THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `K1:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC;
    (* Laplacian *)
    REWRITE_TAC[rfs_sup_lt] THEN EXISTS_TAC `K2 / cR pow 2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC STDCAP_DIV_LE2 THEN
    FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `K2:real`)) (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `KR:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

