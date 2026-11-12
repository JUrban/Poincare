(* ========================================================================= *)
(* Unit pc_p2a_rva: leaf L6 P2A_RVI_ASYMP (MT Prop 6.78, whose convergence   *)
(* of the Jacobians needs C^1 convergence of the L-exponential maps, and     *)
(* Lemma 6.75): the reduced-volume integrand b^(-n/2) exp(-l~(Z,b)) J(Z,b)   *)
(* tends to 2^n exp(-|Z|^2) as b tends to 0. Route: the start window of      *)
(* pc_p2a_lmono (P2AL_SWIN_SETUP: base s1 = 0, initial state (phi x, 2 Z)),  *)
(* whose Jacobi data satisfy Y(s)/s -> 2 I (P2AL_J0_MQUOT); J through        *)
(* P2AL_WOK_J; l~ through P2AL_LTIL_INT and the value 2 |Z|^2 of the s-form  *)
(* integrand at s = 0; the density factor by continuity of the region metric *)
(* along the window flow.  The proofs are generic in N; the 3-d leaf is the  *)
(* instance N = 3.                                                           *)
(*                                                                           *)
(* First: the s-form integrand at s = 0 and the limit of l~.                 *)
(* ========================================================================= *)

needs "src/pc_p2a_lmono.ml";;

prioritize_real();;
type_invention_error := true;;

(* The s-form L-integrand of the L-geodesic from x with initial vector Z    *)
(* is 2 |Z|^2 at s = 0 (its s-velocity there is 2 Z, the scalar term has  *)
(* the factor s^2).                                                          *)

let P2AV_LSINT_ZERO = prove
 (`!(V:p2alv) tt (x:A) Z b.
     Z IN p2a_Ldom V tt x b
     ==> p2a_lsint V tt (p2a_Lgeo V tt x Z b) b (&0) = &2 * p2a_znorm2 V tt x Z`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP P2A_LGEO_PROP) THEN
  ABBREV_TAC `gamma = p2a_Lgeo (V:p2alv) tt (x:A) Z b` THEN
  REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\v. SND(chart_at (p2a_vatlas (V:p2alv) tt) (x:A)) ((gamma:real->A)(drop v pow 2)))
      (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b}) = &2 % Z`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2A_SDOM_INTERVAL; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    REWRITE_TAC[DROP_VEC; LIFT_DROP; IN_INTERVAL_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "has_vector_derivative"))
          (concl th))) THEN
    ASM_SIMP_TAC[P2A_SDOM_INTERVAL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[p2a_lsint; p2a_znorm2; LIFT_NUM; REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_LMUL; DOT_RMUL] THEN REAL_ARITH_TAC);;

(* l~(Z,s^2) tends to |Z|^2 as s tends to 0 from above: l~ = L~/(2 s) and  *)
(* L~(Z,s^2) is the integral over [0,s] of a continuous integrand with      *)
(* value 2 |Z|^2 at 0 (P2AL_LTIL_INT, P2AL_LSINT_CONT).                      *)

let P2AV_LTIL_LIM = prove
 (`!(V:p2alv) tt (x:A) Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> ((\s. p2a_ltil V tt x (s pow 2) Z) ---> p2a_znorm2 V tt x Z)
         (atreal (&0) within {s | &0 < s})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`] P2A_LGEOD_EXISTS_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sqrt b` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `h = p2a_lsint (V:p2alv) tt (p2a_Lgeo V tt (x:A) Z b) b` THEN
  SUBGOAL_THEN `(h:real->real) real_continuous_on real_interval[&0,sqrt b]` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC P2AL_LSINT_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real->real)(&0) = &2 * p2a_znorm2 (V:p2alv) tt (x:A) Z` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC P2AV_LSINT_ZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `&0`; `sqrt b`] REAL_INTEGRAL_HAS_REAL_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_WITHINREAL; REALLIM_WITHINREAL; IN_REAL_INTERVAL] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL; REAL_SUB_RZERO] THEN DISCH_TAC THEN
  REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&2 * e`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (sqrt b)` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 <= b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `b:real`; `Z:real^N`; `s:real`] P2AL_LTIL_INT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[p2a_ltil; POW_2_SQRT; REAL_LT_IMP_LE] THEN
  ABBREV_TAC `q = real_integral (real_interval[&0,s]) (h:real->real)` THEN
  SUBGOAL_THEN `q / (&2 * s) = (q / s) / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The two factors of J in the start window.  The density sqrt(det G(tt -    *)
(* s^2, y(s))) of the region metric along the window flow tends to the       *)
(* density of g(tt) at x (continuity of the s-family across s = 0,           *)
(* P2AL_LWIN_FACTS); abs(det Y(s)) / s^n tends to abs(c)^n for Jacobi data   *)
(* with Y(s)/s -> c I (P2AL_J0_MQUOT).                                       *)
(* ------------------------------------------------------------------------- *)

let P2AV_SWIN_DENS_LIM = prove
 (`!(V:p2alv) tt (x:A) W a U (phi:A->real^N) Z.
     p2a_region V W a tt /\ x IN W /\ chart_at (p2a_vatlas V tt) x = (U,phi) /\
     p2al_lin V tt (&0) (sqrt(tt - a)) W tt U phi (\Z. pastecart (phi x) (&2 % Z)) Z (&0)
     ==> ((\s. sqrt(det(p2a_rlocal V W tt (U INTER W,phi) (tt - s pow 2)
                         (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a)) W tt U phi
                                    (\Z. pastecart (phi x) (&2 % Z)) Z s)))))
          ---> p2a_zdens V tt x) (atreal (&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W:A->bool`; `a:real`; `U:A->bool`;
                 `phi:A->real^N`] P2AL_SWIN_WOK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r = sqrt(tt - a)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  ABBREV_TAC `Phi = \Z:real^N. pastecart ((phi:A->real^N) x) (&2 % Z)` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `p2al_lwa (V:p2alv) tt (&0) r W a tt U (phi:A->real^N) (:real^N) Phi`
  ASSUME_TAC THENL [ASM_MESON_TAC[p2al_wok]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_MESON_TAC[p2al_lwa]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP P2AL_LWIN_FACTS) THEN
  REWRITE_TAC[p2a_lsmooth] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `r:real`; `W:A->bool`; `a:real`; `tt:real`;
                 `U:A->bool`; `phi:A->real^N`; `(:real^N)`; `Phi:real^N->real^(N,N)finite_sum`;
                 `Z:real^N`; `&0`] P2AL_WIN_FLCONT) THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `&0`; `r:real`; `W:A->bool`; `a:real`; `tt:real`;
                 `U:A->bool`; `phi:A->real^N`; `(:real^N)`; `Phi:real^N->real^(N,N)finite_sum`;
                 `Z:real^N`; `&0`] P2AL_LFL_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `fstcart(p2al_lfl (V:p2alv) tt (&0) r W tt U (phi:A->real^N) Phi Z (&0)) = phi x`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Phi" THEN BETA_TAC THEN REWRITE_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  ABBREV_TAC `M = \s. p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N) (tt - s pow 2)
                        (fstcart(p2al_lfl V tt (&0) r W tt U phi Phi Z s))` THEN
  SUBGOAL_THEN
   `(\s. sqrt(det(p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N) (tt - s pow 2)
                    (fstcart(p2al_lfl V tt (&0) r W tt U phi Phi Z s))))) =
    (\s. sqrt(det((M:real->real^N^N) s)))`
  SUBST1_TAC THENL [EXPAND_TAC "M" THEN REWRITE_TAC[]; ALL_TAC] THEN
  (* the value at s = 0 *)
  SUBGOAL_THEN `sqrt(det((M:real->real^N^N)(&0))) = p2a_zdens (V:p2alv) tt (x:A)`
  (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "M" THEN BETA_TAC THEN REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_SUB_RZERO] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:p2alv`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                  P2A_REGION_SLICE) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN topspace(p2a_vtop (V:p2alv) tt)` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:p2alv) tt`; `p2a_vatlas (V:p2alv) tt`; `x:A`] CHART_AT) THEN
    ASM_REWRITE_TAC[FST] THEN STRIP_TAC THEN
    REWRITE_TAC[p2a_rlocal; p2a_rmetric; ETA_AX] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:p2alv) tt`; `p2a_vatlas (V:p2alv) tt`; `U:A->bool`;
                   `phi:A->real^N`; `W:A->bool`; `p2a_vmetric (V:p2alv) tt`; `x:A`]
                  METRIC_LOCAL_RESTRICT) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[p2a_zdens; mfd_density; SND];
    ALL_TAC] THEN
  (* continuity of the region metric along the window flow at s = 0 *)
  SUBGOAL_THEN
   `(\v. vectorize((M:real->real^N^N)(drop v))) continuous (at (lift(&0)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\v. vectorize((M:real->real^N^N)(drop v))) =
      (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
             (p2a_rlocal (V:p2alv) W tt (U INTER W,phi:A->real^N)
                (tt - drop(fstcart z) pow 2) (sndcart z))) o
      (\v. pastecart v (fstcart(p2al_lfl V tt (&0) r W tt U phi Phi Z (drop v))))`
    SUBST1_TAC THENL
     [EXPAND_TAC "M" THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART;
                                      SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_PASTECART THEN REWRITE_TAC[CONTINUOUS_AT_ID] THEN
      SUBGOAL_THEN
       `(\v. fstcart(p2al_lfl (V:p2alv) tt (&0) r W tt U (phi:A->real^N) Phi Z (drop v))) =
        fstcart o (\v. p2al_lfl V tt (&0) r W tt U phi Phi Z (drop v))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_FSTCART];
      ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "smooth_map_on"))
          (concl th))) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `open(interval(lift(&0 - r),lift(&0 + r)) PCROSS IMAGE (phi:A->real^N) (U INTER W))`
    ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\v. lift(det((M:real->real^N^N)(drop v)))) continuous (at (lift(&0)))`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_LIFT_DET THEN
    UNDISCH_TAC `(\v. vectorize((M:real->real^N^N)(drop v))) continuous (at (lift(&0)))` THEN
    REWRITE_TAC[GSYM CONTINUOUS_MATRIX_VECTORIZE; CONTINUOUS_MATRIX_COMPONENTWISE] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_AT; LIFT_DROP] THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
  REWRITE_TAC[REAL_CONTINUOUS_AT_SQRT] THEN
  ASM_REWRITE_TAC[REALLIM_ATREAL_AT; TENDSTO_REAL; o_DEF; LIFT_DROP]);;

let P2AV_J0_DET_LIM = prove
 (`!(Y:real->real^N^N) B c.
     p2al_j0 Y B c
     ==> ((\t. abs(det(Y t)) / t pow dimindex(:N)) ---> abs c pow dimindex(:N))
         (atreal (&0) within {t | &0 < t})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((\t. det(inv t %% (Y:real->real^N^N) t)) --->
                 det(c %% mat 1:real^N^N)) (atreal (&0) within {t | &0 < t})`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN `x:real^N` o MATCH_MP P2AL_J0_MQUOT) THEN
    REWRITE_TAC[LIM_MATRIX_COMPONENTWISE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_LIFT_DET) THEN
    REWRITE_TAC[TENDSTO_REAL; o_DEF];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REALLIM_ABS) THEN
  REWRITE_TAC[DET_CMUL; DET_I; REAL_MUL_RID; REAL_ABS_POW] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM] THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_INV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
  REWRITE_TAC[REAL_POW_INV; real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Assembly.  In the start window, for 0 < s < e0, rvi(s^2) = exp(-l~(s^2))  *)
(* (abs(det Y(s)) / s^n) (sqrt(det G) / zdens) (P2AL_WOK_J); the three       *)
(* factors converge (the two previous sections), and b = s^2 moves the limit *)
(* to b (REALLIM_COMPOSE_WITHIN with sqrt).  L6 is the case N = 3.           *)
(* ------------------------------------------------------------------------- *)

let P2AV_RVI_LIM_S = prove
 (`!(V:p2alv) tt (x:A) Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> ((\s. p2a_rvi V tt x (s pow 2) Z) --->
          &2 pow dimindex(:N) * exp(--(p2a_znorm2 V tt x Z)))
         (atreal (&0) within {s | &0 < s})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`] P2AL_SWIN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:A->bool` (X_CHOOSE_THEN `a0:real` (X_CHOOSE_THEN `U0:A->bool`
    (X_CHOOSE_THEN `phi0:A->real^N` (X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`] P2AL_ZDENS_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`] P2AV_LTIL_LIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `W0:A->bool`; `a0:real`; `U0:A->bool`;
                 `phi0:A->real^N`; `Z:real^N`] P2AV_SWIN_DENS_LIM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2AV_J0_DET_LIM) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&2 pow dimindex(:N) * exp(--(p2a_znorm2 (V:p2alv) tt (x:A) Z)) =
    exp(--(p2a_znorm2 V tt x Z)) *
    (abs(&2) pow dimindex(:N) * (p2a_zdens V tt x / p2a_zdens V tt x))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_ABS_NUM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC
   `\s. exp(--(p2a_ltil (V:p2alv) tt (x:A) (s pow 2) Z)) *
        (abs(det(p2al_jy V tt (&0) (sqrt(tt - a0)) W0 tt U0 (phi0:A->real^N)
                   (\Z. pastecart (phi0 x) (&2 % Z)) Z s)) / s pow dimindex(:N) *
         (sqrt(det(p2a_rlocal V W0 tt (U0 INTER W0,phi0) (tt - s pow 2)
                     (fstcart(p2al_lfl V tt (&0) (sqrt(tt - a0)) W0 tt U0 phi0
                                (\Z. pastecart (phi0 x) (&2 % Z)) Z s)))) /
          p2a_zdens V tt x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `&0`; `sqrt(tt - a0)`; `W0:A->bool`;
                   `a0:real`; `tt:real`; `U0:A->bool`; `phi0:A->real^N`; `(:real^N)`;
                   `\Z:real^N. pastecart ((phi0:A->real^N) x) (&2 % Z)`; `Z:real^N`; `s:real`]
                  P2AL_WOK_J) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIV] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      DISCH_TAC] THEN
    ASM_SIMP_TAC[p2a_rvi; POW_2_SQRT; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `~(s pow dimindex(:N) = &0) /\ ~(p2a_zdens (V:p2alv) tt (x:A) = &0)`
    MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_NZ; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_REAL_CONTINUOUS_FUNCTION THEN
    REWRITE_TAC[REAL_CONTINUOUS_AT_EXP] THEN MATCH_MP_TAC REALLIM_NEG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_DIV THEN ASM_SIMP_TAC[REALLIM_CONST; REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN ASM_REWRITE_TAC[]);;

(* The limit in b = s^2.                                                     *)

let P2AV_RVI_ASYMP_GEN = prove
 (`!(V:p2alv) tt (x:A) Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt
     ==> ((\b. p2a_rvi V tt x b Z) --->
          &2 pow dimindex(:N) * exp(--(p2a_znorm2 V tt x Z)))
         (atreal (&0) within {b | &0 < b})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:p2alv`; `tt:real`; `x:A`; `Z:real^N`] P2AV_RVI_LIM_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `(\s. p2a_rvi (V:p2alv) tt (x:A) (s pow 2) Z) o sqrt` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM; o_THM] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_COMPOSE_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`{s:real | &0 < s}`; `&0`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
    MP_TAC(SPEC `&0` REAL_CONTINUOUS_AT_SQRT) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL; SQRT_0];
    REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ]]);;

(* L6 (P2A_RVI_ASYMP_STATEMENT, pc_p2a_defs): the case N = 3, 2^3 = 8.      *)

let P2AV_RVI_ASYMP = prove
 (`!u:A->bool. P2A_RVI_ASYMP_STATEMENT u`,
  REWRITE_TAC[P2A_RVI_ASYMP_STATEMENT; GSYM P2A_VIEW_PROJ_3] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 pow dimindex(:3) = &8` (fun th -> REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC P2AV_RVI_ASYMP_GEN THEN ASM_REWRITE_TAC[]);;

