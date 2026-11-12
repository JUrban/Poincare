(* ========================================================================= *)
(* Unit pc_rfa_slbar: the local barrier argument for the local Shi estimates *)
(* (CLN Lemma 6.19 and the first-touching argument of Step 4 of the proof of *)
(* Thm 6.15): a quantity with dF/dt <= Lap F - delta F^2 + D is dominated by *)
(* the barrier Bc / psi^2 + 1/(delta (t - sigma)) + Lam on the support of a  *)
(* cutoff psi, as long as the cutoff has controlled gradient and Laplacian   *)
(* (a bootstrap hypothesis).                                                 *)
(* ========================================================================= *)

needs "src/pc_rfa_slcalc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Real-variable helpers: the first time of a closed bad set,                *)
(* one-sided derivative and continuity tests, the derivatives of the        *)
(* barrier profile.                                                          *)
(* ========================================================================= *)

let RFA_FIRST_TIME = prove
 (`!P (Q:real^(1,N)finite_sum->real).
     compact P /\ (\w. lift(Q w)) continuous_on P /\ (?w. w IN P /\ &0 <= Q w)
     ==> ?w0. w0 IN P /\ &0 <= Q w0 /\
              !w. w IN P /\ &0 <= Q w ==> drop(fstcart w0) <= drop(fstcart w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact {w | w IN P /\ &0 <= (Q:real^(1,N)finite_sum->real) w}`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `P:real^(1,N)finite_sum->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{w | w IN P /\ &0 <= (Q:real^(1,N)finite_sum->real) w} =
      {w | w IN P /\ (\w. lift(Q w)) w IN {x:real^1 | x$1 >= &0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_ge]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_HALFSPACE_COMPONENT_GE];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `IMAGE (\w. drop(fstcart w)) {w | w IN P /\ &0 <= (Q:real^(1,N)finite_sum->real) w}`
   COMPACT_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; ETA_AX] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `w:real^(1,N)finite_sum` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let RFA_DERIV_NONNEG_LEFT = prove
 (`!f f' t0 d.
     (f has_real_derivative f') (atreal t0) /\ &0 < d /\
     (!t. t0 - d < t /\ t < t0 ==> f t < f t0)
     ==> &0 <= f'`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `f' < &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `f':real`; `t0:real`; `(:real)`; `--f' / &2`]
         RFA_LEFT_DERIV_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[WITHINREAL_UNIV] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 - min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `min e d / &2 * f' < &0` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `abs(f t0 - f(t0 - min e d / &2) - min e d / &2 * f') <=
               --f' / &2 * min e d / &2` THEN
  UNDISCH_TAC `(f:real->real)(t0 - min e d / &2) < f t0` THEN
  REAL_ARITH_TAC);;

let RFA_CONT_LEFT_LE = prove
 (`!f t0 d.
     f real_continuous (atreal t0) /\ &0 < d /\
     (!t. t0 - d < t /\ t < t0 ==> f t < &0)
     ==> f t0 <= &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < (f:real->real) t0` THENL
   [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_CONTINUOUS_ATREAL]) THEN
  REWRITE_TAC[REALLIM_ATREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real->real) t0`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 - min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t0 - min e d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The barrier profile Bc / x^2 + c and its derivatives; the                 *)
(* Laplacian of Bc / psi^2; the supersolution inequality (CLN Lemma 6.19).   *)
(* ========================================================================= *)

let RFA_HRD_EQ = prove
 (`!f a b net. (f has_real_derivative a) net ==> a = b ==> (f has_real_derivative b) net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let RFA_INVSQ_D1 = prove
 (`!Bc c x. &0 < x
     ==> ((\x. Bc * inv(x pow 2) + c) has_real_derivative --(&2 * Bc * inv(x pow 3)))
         (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\x. Bc * inv(x pow 2) + c) has_real_derivative f') (atreal x)`)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP RFA_HRD_EQ) THEN
  UNDISCH_TAC `&0 < x` THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD);;

let RFA_INVSQ_D2 = prove
 (`!Bc x. &0 < x
     ==> ((\x. --(&2 * Bc * inv(x pow 3))) has_real_derivative &6 * Bc * inv(x pow 4))
         (atreal x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\x. --(&2 * Bc * inv(x pow 3))) has_real_derivative f') (atreal x)`)) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH]; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP RFA_HRD_EQ) THEN
  UNDISCH_TAC `&0 < x` THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD);;

let RFA_BARRIER_TIME_D = prove
 (`!Bc p delta sigma Lam t.
     &0 < delta /\ sigma < t
     ==> ((\t. Bc * inv(p pow 2) + inv(delta * (t - sigma)) + Lam) has_real_derivative
          --inv(delta * (t - sigma) pow 2)) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(DISCH_ALL(REAL_DIFF_CONV
    `((\t. Bc * inv(p pow 2) + inv(delta * (t - sigma)) + Lam) has_real_derivative f')
     (atreal t)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP RFA_HRD_EQ) THEN
  UNDISCH_TAC `&0 < delta` THEN UNDISCH_TAC `sigma < t` THEN
  CONV_TAC REAL_FIELD);;

let RFA_LLAP_INVSQ = prove
 (`!V (G0:real^N->real^N^N) psi z Bc c.
     open V /\ smooth_map_on V (\w. lift(psi w)) /\ z IN V /\ (!w. w IN V ==> &0 < psi w)
     ==> llap G0 (\w. Bc * inv(psi w pow 2) + c) z =
         --(&2 * Bc * inv(psi z pow 3)) * llap G0 psi z +
         &6 * Bc * inv(psi z pow 4) * lgrad2 G0 psi z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`V:real^N->bool`; `{x:real | &0 < x}`; `G0:real^N->real^N^N`; `psi:real^N->real`;
    `\x. Bc * inv(x pow 2) + c`; `\x. --(&2 * Bc * inv(x pow 3))`;
    `\x. &6 * Bc * inv(x pow 4)`; `z:real^N`] RFA_LLAP_COMPOSE)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IN_ELIM_THM; RFA_INVSQ_D1; RFA_INVSQ_D2];
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]);;

let RFA_SUPERSOL_ALG = prove
 (`!p Lp g2 Bc delta s Lam D beta2 gam.
     &0 < p /\ &0 <= g2 /\ g2 <= beta2 /\ --(p * Lp) <= gam /\ &0 < delta /\ &0 < s /\
     &0 < Bc /\ &0 <= Lam /\ D <= delta * Lam pow 2 /\ &2 * gam + &6 * beta2 < delta * Bc
     ==> (--(&2 * Bc * inv(p pow 3)) * Lp + &6 * Bc * inv(p pow 4) * g2) -
         delta * (Bc * inv(p pow 2) + inv(delta * s) + Lam) pow 2 + D
         < --inv(delta * s pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = inv(p pow 4)` THEN ABBREV_TAC `X = Bc * inv(p pow 2)` THEN
  ABBREV_TAC `Y = inv(delta * s)` THEN
  SUBGOAL_THEN `&0 < q /\ &0 <= X /\ &0 <= Y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "X"; "Y"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                                                 REAL_POW_LE];
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta * (X pow 2 + Y pow 2 + Lam pow 2) <= delta * (X + Y + Lam) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 <= X * Y /\ &0 <= X * Lam /\ &0 <= Y * Lam` MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&2 * Bc * inv(p pow 3)) * Lp = &2 * Bc * q * --(p * Lp)` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `delta * X pow 2 = delta * Bc pow 2 * q` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "q"] THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `delta * Y pow 2 = inv(delta * s pow 2)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN UNDISCH_TAC `&0 < delta` THEN UNDISCH_TAC `&0 < s` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Bc * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(Bc * q) * --(p * Lp) <= (Bc * q) * gam` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Bc * q) * g2 <= (Bc * q) * beta2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `Bc * q * (&2 * gam + &6 * beta2 - delta * Bc) < &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y * z < &0 <=> &0 < (x * y) * --z`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta * Lam pow 2 = delta * Lam pow 2` (K ALL_TAC) THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`Bc * q * (&2 * gam + &6 * beta2 - delta * Bc) < &0`;
    `delta * (X pow 2 + Y pow 2 + Lam pow 2) <= delta * (X + Y + Lam) pow 2`;
    `(Bc * q) * g2 <= (Bc * q) * beta2`;
    `(Bc * q) * --(p * Lp) <= (Bc * q) * gam`;
    `delta * Y pow 2 = inv(delta * s pow 2)`; `delta * X pow 2 = delta * Bc pow 2 * q`;
    `D <= delta * Lam pow 2`] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Smoothness of the barrier in space, continuity of the                     *)
(* weighted excess Q, and the first touching point.                          *)
(* ========================================================================= *)

let RFA_INVSQ_SMOOTH = prove
 (`!V (psi:real^N->real) Bc c.
     open V /\ smooth_map_on V (\z. lift(psi z)) /\ (!z. z IN V ==> &0 < psi z)
     ==> smooth_map_on V (\z. lift(Bc * inv(psi z pow 2) + c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `\z:real^N. lift(Bc * inv((psi:real^N->real) z pow 2))`;
                 `\z:real^N. lift c`] SMOOTH_MAP_ON_LIFT_ADD) THEN
  REWRITE_TAC[LIFT_DROP; SMOOTH_MAP_ON_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `Bc:real`;
                 `\z:real^N. lift(inv((psi:real^N->real) z pow 2))`] SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `\z:real^N. lift((psi:real^N->real) z pow 2)`]
         SMOOTH_MAP_ON_LIFT_INV) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `\z:real^N. lift((psi:real^N->real) z)`; `2`]
           SMOOTH_MAP_ON_LIFT_POW) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ; ARITH]]);;

let RFA_BARRIER_Q_CONT = prove
 (`!U Kc (Fq:real->real^N->real) psi sigma tau eps delta Bc Lam.
     Kc SUBSET U /\ (\z. lift(psi z)) continuous_on U /\ &0 < eps /\ &0 < delta /\
     (\w. lift(Fq (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift sigma,lift tau] PCROSS Kc)
     ==> (\w. lift(psi(sndcart w) pow 2 *
                   (Fq (drop(fstcart w)) (sndcart w) -
                    inv(delta * (drop(fstcart w) - sigma)) - Lam) - Bc))
         continuous_on (interval[lift(sigma + eps),lift tau] PCROSS Kc)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = interval[lift(sigma + eps),lift tau] PCROSS (Kc:real^N->bool)` THEN
  SUBGOAL_THEN `P SUBSET interval[lift sigma,lift tau] PCROSS (Kc:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN P ==> sigma + eps <= drop(fstcart(w:real^(1,N)finite_sum)) /\
                               sndcart w IN (Kc:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w. lift((psi:real^N->real)(sndcart(w:real^(1,N)finite_sum)))) continuous_on P`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w. lift((psi:real^N->real)(sndcart(w:real^(1,N)finite_sum)))) =
                  (\z. lift(psi z)) o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_SNDCART];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift(inv(delta * (drop(fstcart(w:real^(1,N)finite_sum)) - sigma)))) continuous_on P`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\w. lift(inv(delta * (drop(fstcart(w:real^(1,N)finite_sum)) - sigma)))) =
      lift o inv o (\w. delta * (drop(fstcart w) - sigma))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_CMUL; LIFT_SUB; LIFT_DROP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[LINEAR_FSTCART; ETA_AX];
      X_GEN_TAC `w:real^(1,N)finite_sum` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^(1,N)finite_sum`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `interval[lift sigma,lift tau] PCROSS (Kc:real^N->bool)` THEN
  ASM_REWRITE_TAC[]);;

let RFA_Q_IFF = prove
 (`!p f Bc i l. &0 < p
                ==> (&0 <= p * (f - i - l) - Bc <=> Bc * inv(p) + i + l <= f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x - Bc <=> Bc <= x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let RFA_BARRIER_FIRST = prove
 (`!U Kc (Fq:real->real^N->real) psi sigma tau delta Bc Lam t1 z1.
     open U /\ compact Kc /\ Kc SUBSET U /\ sigma < tau /\
     (\z. lift(psi z)) continuous_on U /\
     (!z. z IN U ==> &0 <= psi z) /\ (!z. z IN U /\ ~(z IN Kc) ==> psi z = &0) /\
     (\w. lift(Fq (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift sigma,lift tau] PCROSS Kc) /\
     (!t z. sigma < t /\ t <= tau /\ z IN U ==> (\s. Fq s z) real_continuous atreal t) /\
     &0 < delta /\ &0 < Bc /\ &0 <= Lam /\
     sigma < t1 /\ t1 <= tau /\ z1 IN U /\ &0 < psi z1 /\
     Bc * inv(psi z1 pow 2) + inv(delta * (t1 - sigma)) + Lam <= Fq t1 z1
     ==> ?t0 z0. sigma < t0 /\ t0 <= tau /\ z0 IN U /\ &0 < psi z0 /\
                 Fq t0 z0 = Bc * inv(psi z0 pow 2) + inv(delta * (t0 - sigma)) + Lam /\
                 (!t z. sigma < t /\ t < t0 /\ z IN U /\ &0 < psi z
                        ==> Fq t z < Bc * inv(psi z pow 2) + inv(delta * (t - sigma)) +
                                     Lam) /\
                 (!z. z IN U /\ &0 < psi z
                      ==> Fq t0 z <= Bc * inv(psi z pow 2) + inv(delta * (t0 - sigma)) +
                                     Lam)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "oU cK KU st psc psp psz Fc Fct dpos Bpos Lpos t1a t1b z1U psz1 bad" THEN
  SUBGOAL_THEN
   `?M. &0 < M /\
        !t z. sigma <= t /\ t <= tau /\ z IN Kc ==> (Fq:real->real^N->real) t z <= M`
  (X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Mb"))) THENL
   [MP_TAC(ISPECL [`\w. lift((Fq:real->real^N->real) (drop(fstcart w)) (sndcart w))`;
                   `interval[lift sigma,lift tau] PCROSS (Kc:real^N->bool)`]
           COMPACT_CONTINUOUS_IMAGE) THEN
    ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift t) (z:real^N)`) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                SNDCART_PASTECART; NORM_LIFT] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eps = inv(delta * (M + &1))` THEN
  SUBGOAL_THEN `&0 < eps` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. sigma < t /\ t <= tau /\ t <= sigma + eps /\ z IN Kc
          ==> (Fq:real->real^N->real) t z <
              Bc * inv(psi z pow 2) + inv(delta * (t - sigma)) + Lam`
  (LABEL_TAC "early") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `M + &1 <= inv(delta * (t - sigma))` ASSUME_TAC THENL
     [SUBGOAL_THEN `M + &1 = inv(delta * eps)` SUBST1_TAC THENL
       [EXPAND_TAC "eps" THEN UNDISCH_TAC `&0 < delta` THEN UNDISCH_TAC `&0 < M` THEN
        CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Bc * inv((psi:real^N->real) z pow 2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_LE_POW_2];
      ALL_TAC] THEN
    USE_THEN "Mb" (MP_TAC o SPECL [`t:real`; `z:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z1:real^N) IN Kc` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `sigma + eps < t1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "early" (MP_TAC o SPECL [`t1:real`; `z1:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "bad" MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval[lift(sigma + eps),lift tau] PCROSS (Kc:real^N->bool)`;
    `\w. (psi:real^N->real)(sndcart w) pow 2 *
         ((Fq:real->real^N->real) (drop(fstcart w)) (sndcart w) -
          inv(delta * (drop(fstcart w) - sigma)) - Lam) - Bc`] RFA_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL];
      MATCH_MP_TAC RFA_BARRIER_Q_CONT THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `pastecart (lift t1) (z1:real^N)` THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; RFA_Q_IFF; REAL_POW_LT]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^(1,N)finite_sum`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "min")))) THEN
  SUBST1_TAC(SYM(ISPEC `w0:real^(1,N)finite_sum` PASTECART_FST_SND)) THEN
  ABBREV_TAC `t0 = drop(fstcart(w0:real^(1,N)finite_sum))` THEN
  ABBREV_TAC `z0:real^N = sndcart(w0:real^(1,N)finite_sum)` THEN
  SUBGOAL_THEN `fstcart(w0:real^(1,N)finite_sum) = lift t0` SUBST1_TAC THENL
   [EXPAND_TAC "t0" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
              SNDCART_PASTECART] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z0:real^N) IN U` ASSUME_TAC THENL
   [UNDISCH_TAC `Kc SUBSET (U:real^N->bool)` THEN UNDISCH_TAC `(z0:real^N) IN Kc` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (psi:real^N->real) z0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    CONJ_TAC THENL [USE_THEN "psp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC
     `&0 <= (psi:real^N->real) z0 pow 2 *
            ((Fq:real->real^N->real) t0 z0 - inv(delta * (t0 - sigma)) - Lam) - Bc` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. sigma < t /\ t < t0 /\ z IN U /\ &0 < psi z
          ==> (Fq:real->real^N->real) t z <
              Bc * inv(psi z pow 2) + inv(delta * (t - sigma)) + Lam`
  (LABEL_TAC "before") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN Kc` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    ASM_CASES_TAC `t <= sigma + eps` THENL
     [USE_THEN "early" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPEC `pastecart (lift t) (z:real^N)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[RFA_Q_IFF; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN U /\ &0 < psi z
        ==> (Fq:real->real^N->real) t0 z <=
            Bc * inv(psi z pow 2) + inv(delta * (t0 - sigma)) + Lam`
  (LABEL_TAC "at") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\t. (Fq:real->real^N->real) t z -
                        (Bc * inv((psi:real^N->real) z pow 2) +
                         inv(delta * (t - sigma)) + Lam)`;
                   `t0:real`; `t0 - sigma`] RFA_CONT_LEFT_LE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN CONJ_TAC THENL
        [USE_THEN "Fct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
         MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
         EXISTS_TAC `--inv(delta * (t0 - sigma) pow 2)` THEN
         MATCH_MP_TAC RFA_BARRIER_TIME_D THEN ASM_REAL_ARITH_TAC];
       ASM_REAL_ARITH_TAC;
       X_GEN_TAC `t:real` THEN STRIP_TAC THEN
       MATCH_MP_TAC(REAL_ARITH `x < y ==> x - y < &0`) THEN
       USE_THEN "before" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t0:real`; `z0:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [USE_THEN "at" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `&0 <= (psi:real^N->real) z0 pow 2 *
            ((Fq:real->real^N->real) t0 z0 - inv(delta * (t0 - sigma)) - Lam) - Bc` THEN
    ASM_SIMP_TAC[RFA_Q_IFF; REAL_POW_LT]]);;

(* ========================================================================= *)
(* The local barrier theorem.                                                *)
(* ========================================================================= *)

let RFA_LOCAL_BARRIER = prove
 (`!U Kc (G:real->real^N->real^N^N) (Fq:real->real^N->real) psi a b sigma tau
    delta D Bc Lam beta2 gam.
     open U /\ compact Kc /\ Kc SUBSET U /\ a < sigma /\ sigma < tau /\ tau < b /\
     (!t. a < t /\ t < b ==> metric_field U (G t)) /\
     smooth_map_on U (\z. lift(psi z)) /\
     (!z. z IN U ==> &0 <= psi z) /\ (!z. z IN U /\ ~(z IN Kc) ==> psi z = &0) /\
     (\w. lift(Fq (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift sigma,lift tau] PCROSS Kc) /\
     (!t. sigma < t /\ t <= tau ==> smooth_map_on U (\z. lift(Fq t z))) /\
     (!t z. sigma < t /\ t <= tau /\ z IN U
            ==> ?dF. ((\s. Fq s z) has_real_derivative dF) (atreal t) /\
                     dF <= llap (G t) (Fq t) z - delta * (Fq t z) pow 2 + D) /\
     (!t0 z. sigma < t0 /\ t0 <= tau /\ z IN U /\ &0 < psi z /\
             (!t. sigma < t /\ t <= t0
                  ==> Fq t z <= Bc * inv(psi z pow 2) + inv(delta * (t - sigma)) + Lam)
             ==> lgrad2 (G t0) psi z <= beta2 /\ --(psi z * llap (G t0) psi z) <= gam) /\
     &0 < delta /\ &0 < Bc /\ &0 <= Lam /\ D <= delta * Lam pow 2 /\
     &2 * gam + &6 * beta2 < delta * Bc
     ==> !t z. sigma < t /\ t <= tau /\ z IN U /\ &0 < psi z
               ==> Fq t z < Bc * inv(psi z pow 2) + inv(delta * (t - sigma)) + Lam`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "oU cK KU as st tb mf psm psp psz Fc Fs Fev cut dpos Bpos Lpos DL sup" THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `(Fq:real->real^N->real) t z <
    Bc * inv(psi z pow 2) + inv(delta * (t - sigma)) + Lam` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\z. lift((psi:real^N->real) z)) continuous_on U` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. sigma < t /\ t <= tau /\ z IN U
          ==> (\s. (Fq:real->real^N->real) s z) real_continuous atreal t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "Fev" (MP_TAC o SPECL [`t':real`; `z':real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MESON_TAC[HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `Kc:real^N->bool`; `Fq:real->real^N->real`;
                 `psi:real^N->real`; `sigma:real`; `tau:real`; `delta:real`; `Bc:real`;
                 `Lam:real`; `t:real`; `z:real^N`] RFA_BARRIER_FIRST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `z0:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "bef")
                     (LABEL_TAC "at"))))))))) THEN
  ABBREV_TAC `c0 = inv(delta * (t0 - sigma)) + Lam` THEN
  SUBGOAL_THEN `metric_field U ((G:real->real^N->real^N^N) t0)` ASSUME_TAC THENL
   [USE_THEN "mf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open {z | z IN U /\ &0 < (psi:real^N->real) z}` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{z | z IN U /\ &0 < (psi:real^N->real) z} =
      {z | z IN U /\ (\z. lift(psi z)) z IN {x:real^1 | x$1 > &0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {z | z IN U /\ &0 < (psi:real^N->real) z} (\z. lift(psi z)) /\
    smooth_map_on {z | z IN U /\ &0 < psi z}
      (\z. lift((Fq:real->real^N->real) t0 z)) /\
    smooth_map_on {z | z IN U /\ &0 < psi z} (\z. lift(Bc * inv(psi z pow 2) + c0))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{z | z IN U /\ &0 < (psi:real^N->real) z} SUBSET U` ASSUME_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "Fs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_INVSQ_SMOOTH THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on {z | z IN U /\ &0 < (psi:real^N->real) z}
      (\w. lift((Fq:real->real^N->real) t0 w - (Bc * inv(psi w pow 2) + c0)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                   `\w. lift((Fq:real->real^N->real) t0 w)`;
                   `\w. lift(Bc * inv((psi:real^N->real) w pow 2) + c0)`]
           SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `llap ((G:real->real^N->real^N^N) t0) (Fq t0) z0 <=
    llap (G t0) (\w. Bc * inv((psi:real^N->real) w pow 2) + c0) z0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                   `(G:real->real^N->real^N^N) t0`;
                   `\w. (Fq:real->real^N->real) t0 w -
                        (Bc * inv((psi:real^N->real) w pow 2) + c0)`; `z0:real^N`]
           RFA_LLAP_LOCAL_MAX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y /\ a = b ==> x - y <= a - b`) THEN
      CONJ_TAC THENL
       [USE_THEN "at" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                   `(G:real->real^N->real^N^N) t0`;
                   `\w. (Fq:real->real^N->real) t0 w`;
                   `\w. Bc * inv((psi:real^N->real) w pow 2) + c0`; `z0:real^N`]
           RFA_LLAP_SUB) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Fev" (MP_TAC o SPECL [`t0:real`; `z0:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dF:real` (CONJUNCTS_THEN2 (LABEL_TAC "dF") (LABEL_TAC "ev"))) THEN
  SUBGOAL_THEN `&0 <= dF - --inv(delta * (t0 - sigma) pow 2)` (LABEL_TAC "nn") THENL
   [MATCH_MP_TAC RFA_DERIV_NONNEG_LEFT THEN
    MAP_EVERY EXISTS_TAC
     [`\s. (Fq:real->real^N->real) s z0 -
           (Bc * inv((psi:real^N->real) z0 pow 2) + inv(delta * (s - sigma)) + Lam)`;
      `t0:real`; `t0 - sigma`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC RFA_BARRIER_TIME_D THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "bef" (MP_TAC o SPECL [`s:real`; `z0:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "eq" MP_TAC THEN
      UNDISCH_TAC `inv(delta * (t0 - sigma)) + Lam = c0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "cut" (MP_TAC o SPECL [`t0:real`; `z0:real^N`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < t0` THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "bef" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `s:real = t0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "eq" MP_TAC THEN
      UNDISCH_TAC `inv(delta * (t0 - sigma)) + Lam = c0` THEN REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g2") (LABEL_TAC "lp"))] THEN
  SUBGOAL_THEN `&0 <= lgrad2 ((G:real->real^N->real^N^N) t0) psi z0` ASSUME_TAC THENL
   [MATCH_MP_TAC LGRAD2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(psi:real^N->real) z0`; `llap ((G:real->real^N->real^N^N) t0) psi z0`;
                 `lgrad2 ((G:real->real^N->real^N^N) t0) psi z0`; `Bc:real`;
                 `delta:real`; `t0 - sigma`; `Lam:real`; `D:real`; `beta2:real`;
                 `gam:real`] RFA_SUPERSOL_ALG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ss") THEN
  MP_TAC(ISPECL [`{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                 `(G:real->real^N->real^N^N) t0`; `psi:real^N->real`; `z0:real^N`;
                 `Bc:real`; `c0:real`] RFA_LLAP_INVSQ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; DISCH_THEN(LABEL_TAC "li")] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  USE_THEN "ev" MP_TAC THEN USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "li" (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  UNDISCH_TAC
   `llap ((G:real->real^N->real^N^N) t0) (Fq t0) z0 <=
    --(&2 * Bc * inv((psi:real^N->real) z0 pow 3)) * llap (G t0) psi z0 +
    &6 * Bc * inv(psi z0 pow 4) * lgrad2 (G t0) psi z0` THEN
  USE_THEN "ss" MP_TAC THEN USE_THEN "nn" MP_TAC THEN
  REAL_ARITH_TAC);;

