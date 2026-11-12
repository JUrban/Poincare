(* ========================================================================= *)
(* Unit pc_rfa_shi329: MT Thm 3.29 (Shi with initial bounds),                *)
(* P2_THM_3_29_STATEMENT, proved as RFA_P2_THM_3_29.  The barrier without    *)
(* the time term, Bc / psi^2 + Lam, started from the initial bounds at       *)
(* sg = a; the normal coordinates are those of g(a), so the balls are at the *)
(* initial time and no ball comparison is needed; continuity at the initial  *)
(* time comes from the chart extensions of ricci_flow_from.                  *)
(* ========================================================================= *)

needs "src/pc_rfa_shi328.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The barrier maximum principle without the time term, from                 *)
(* a strict initial inequality (variants of the lemmas of pc_rfa_slbar).     *)
(* ========================================================================= *)

let RFA_SUPERSOL_ALG0 = prove
 (`!p Lp g2 Bc delta Lam D beta2 gam.
     &0 < p /\ &0 <= g2 /\ g2 <= beta2 /\ --(p * Lp) <= gam /\ &0 < delta /\
     &0 < Bc /\ &0 <= Lam /\ D <= delta * Lam pow 2 /\ &2 * gam + &6 * beta2 < delta * Bc
     ==> (--(&2 * Bc * inv(p pow 3)) * Lp + &6 * Bc * inv(p pow 4) * g2) -
         delta * (Bc * inv(p pow 2) + Lam) pow 2 + D < &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = inv(p pow 4)` THEN ABBREV_TAC `X = Bc * inv(p pow 2)` THEN
  SUBGOAL_THEN `&0 < q /\ &0 <= X` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "X"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                                                 REAL_POW_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `delta * (X pow 2 + Lam pow 2) <= delta * (X + Lam) pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `&0 <= X * Lam` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&2 * Bc * inv(p pow 3)) * Lp = &2 * Bc * q * --(p * Lp)` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `delta * X pow 2 = delta * Bc pow 2 * q` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "q"] THEN UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
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
  MAP_EVERY UNDISCH_TAC
   [`Bc * q * (&2 * gam + &6 * beta2 - delta * Bc) < &0`;
    `delta * (X pow 2 + Lam pow 2) <= delta * (X + Lam) pow 2`;
    `(Bc * q) * g2 <= (Bc * q) * beta2`;
    `(Bc * q) * --(p * Lp) <= (Bc * q) * gam`;
    `delta * X pow 2 = delta * Bc pow 2 * q`;
    `D <= delta * Lam pow 2`] THEN
  REAL_ARITH_TAC);;

let RFA_Q_IFF0 = prove
 (`!p f Bc l. &0 < p ==> (&0 <= p * (f - l) - Bc <=> Bc * inv p + l <= f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `f:real`; `Bc:real`; `&0`; `l:real`] RFA_Q_IFF) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_LID] THEN REWRITE_TAC[REAL_ADD_RID]);;

let RFA_BARRIER_Q_CONT0 = prove
 (`!U Kc (Fq:real->real^N->real) psi sigma tau Bc Lam.
     Kc SUBSET U /\ (\z. lift(psi z)) continuous_on U /\
     (\w. lift(Fq (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift sigma,lift tau] PCROSS Kc)
     ==> (\w. lift(psi(sndcart w) pow 2 *
                   (Fq (drop(fstcart w)) (sndcart w) - Lam) - Bc))
         continuous_on (interval[lift sigma,lift tau] PCROSS Kc)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = interval[lift sigma,lift tau] PCROSS (Kc:real^N->bool)` THEN
  SUBGOAL_THEN `!w. w IN P ==> sndcart(w:real^(1,N)finite_sum) IN (Kc:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
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
  REWRITE_TAC[LIFT_SUB; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST]);;

let RFA_BARRIER_FIRST0 = prove
 (`!U Kc (Fq:real->real^N->real) psi sigma tau Bc Lam t1 z1.
     open U /\ compact Kc /\ Kc SUBSET U /\ sigma < tau /\
     (\z. lift(psi z)) continuous_on U /\
     (!z. z IN U ==> &0 <= psi z) /\ (!z. z IN U /\ ~(z IN Kc) ==> psi z = &0) /\
     (\w. lift(Fq (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift sigma,lift tau] PCROSS Kc) /\
     (!t z. sigma < t /\ t <= tau /\ z IN U ==> (\s. Fq s z) real_continuous atreal t) /\
     &0 < Bc /\
     (!z. z IN U /\ &0 < psi z ==> Fq sigma z < Bc * inv(psi z pow 2) + Lam) /\
     sigma <= t1 /\ t1 <= tau /\ z1 IN U /\ &0 < psi z1 /\
     Bc * inv(psi z1 pow 2) + Lam <= Fq t1 z1
     ==> ?t0 z0. sigma < t0 /\ t0 <= tau /\ z0 IN U /\ &0 < psi z0 /\
                 Fq t0 z0 = Bc * inv(psi z0 pow 2) + Lam /\
                 (!t z. sigma <= t /\ t < t0 /\ z IN U /\ &0 < psi z
                        ==> Fq t z < Bc * inv(psi z pow 2) + Lam) /\
                 (!z. z IN U /\ &0 < psi z ==> Fq t0 z <= Bc * inv(psi z pow 2) + Lam)`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "oU cK KU st psc psp psz Fc Fct Bpos init t1a t1b z1U psz1 bad" THEN
  SUBGOAL_THEN `(z1:real^N) IN Kc` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`interval[lift sigma,lift tau] PCROSS (Kc:real^N->bool)`;
    `\w. (psi:real^N->real)(sndcart w) pow 2 *
         ((Fq:real->real^N->real) (drop(fstcart w)) (sndcart w) - Lam) - Bc`]
   RFA_FIRST_TIME) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL];
      MATCH_MP_TAC RFA_BARRIER_Q_CONT0 THEN EXISTS_TAC `U:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `pastecart (lift t1) (z1:real^N)` THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[RFA_Q_IFF0; REAL_POW_LT]];
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
     `&0 <= (psi:real^N->real) z0 pow 2 * ((Fq:real->real^N->real) t0 z0 - Lam) - Bc` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Bc * inv((psi:real^N->real) z0 pow 2) + Lam <=
                (Fq:real->real^N->real) t0 z0` ASSUME_TAC THENL
   [UNDISCH_TAC
     `&0 <= (psi:real^N->real) z0 pow 2 * ((Fq:real->real^N->real) t0 z0 - Lam) - Bc` THEN
    ASM_SIMP_TAC[RFA_Q_IFF0; REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `sigma < t0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `s <= t /\ ~(t = s) ==> s < t`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "init" (MP_TAC o SPEC `z0:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `Bc * inv((psi:real^N->real) z0 pow 2) + Lam <=
                 (Fq:real->real^N->real) sigma z0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. sigma <= t /\ t < t0 /\ z IN U /\ &0 < psi z
          ==> (Fq:real->real^N->real) t z < Bc * inv(psi z pow 2) + Lam`
  (LABEL_TAC "before") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN Kc` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPEC `pastecart (lift t) (z:real^N)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[RFA_Q_IFF0; REAL_POW_LT] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[FSTCART_PASTECART; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN U /\ &0 < psi z
        ==> (Fq:real->real^N->real) t0 z <= Bc * inv(psi z pow 2) + Lam`
  (LABEL_TAC "at") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\t. (Fq:real->real^N->real) t z -
                        (Bc * inv((psi:real^N->real) z pow 2) + Lam)`;
                   `t0:real`; `t0 - sigma`] RFA_CONT_LEFT_LE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_SUB THEN REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
       USE_THEN "Fct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
       ASM_REAL_ARITH_TAC;
       X_GEN_TAC `t:real` THEN STRIP_TAC THEN
       MATCH_MP_TAC(REAL_ARITH `x < y ==> x - y < &0`) THEN
       USE_THEN "before" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`t0:real`; `z0:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "at" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let RFA_LOCAL_BARRIER0 = prove
 (`!U Kc (G:real->real^N->real^N^N) (Fq:real->real^N->real) psi a b sigma tau
    delta D Bc Lam beta2 gam.
     open U /\ compact Kc /\ Kc SUBSET U /\ a <= sigma /\ sigma < tau /\ tau < b /\
     (!t. a < t /\ t < b ==> metric_field U (G t)) /\
     smooth_map_on U (\z. lift(psi z)) /\
     (!z. z IN U ==> &0 <= psi z) /\ (!z. z IN U /\ ~(z IN Kc) ==> psi z = &0) /\
     (\w. lift(Fq (drop(fstcart w)) (sndcart w))) continuous_on
       (interval[lift sigma,lift tau] PCROSS Kc) /\
     (!t. sigma < t /\ t <= tau ==> smooth_map_on U (\z. lift(Fq t z))) /\
     (!t z. sigma < t /\ t <= tau /\ z IN U
            ==> ?dF. ((\s. Fq s z) has_real_derivative dF) (atreal t) /\
                     dF <= llap (G t) (Fq t) z - delta * (Fq t z) pow 2 + D) /\
     (!z. z IN U /\ &0 < psi z ==> Fq sigma z < Bc * inv(psi z pow 2) + Lam) /\
     (!t0 z. sigma < t0 /\ t0 <= tau /\ z IN U /\ &0 < psi z /\
             (!t. sigma <= t /\ t <= t0 ==> Fq t z <= Bc * inv(psi z pow 2) + Lam)
             ==> lgrad2 (G t0) psi z <= beta2 /\ --(psi z * llap (G t0) psi z) <= gam) /\
     &0 < delta /\ &0 < Bc /\ &0 <= Lam /\ D <= delta * Lam pow 2 /\
     &2 * gam + &6 * beta2 < delta * Bc
     ==> !t z. sigma <= t /\ t <= tau /\ z IN U /\ &0 < psi z
               ==> Fq t z < Bc * inv(psi z pow 2) + Lam`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "oU cK KU as st tb mf psm psp psz Fc Fs Fev init cut dpos Bpos Lpos DL sup" THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `(Fq:real->real^N->real) t z < Bc * inv(psi z pow 2) + Lam` THEN
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
                 `psi:real^N->real`; `sigma:real`; `tau:real`; `Bc:real`;
                 `Lam:real`; `t:real`; `z:real^N`] RFA_BARRIER_FIRST0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real` (X_CHOOSE_THEN `z0:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "bef")
                     (LABEL_TAC "at"))))))))) THEN
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
    smooth_map_on {z | z IN U /\ &0 < psi z} (\z. lift(Bc * inv(psi z pow 2) + Lam))`
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
      (\w. lift((Fq:real->real^N->real) t0 w - (Bc * inv(psi w pow 2) + Lam)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                   `\w. lift((Fq:real->real^N->real) t0 w)`;
                   `\w. lift(Bc * inv((psi:real^N->real) w pow 2) + Lam)`]
           SMOOTH_MAP_ON_LIFT_SUB) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `llap ((G:real->real^N->real^N^N) t0) (Fq t0) z0 <=
    llap (G t0) (\w. Bc * inv((psi:real^N->real) w pow 2) + Lam) z0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^N->bool`; `{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                   `(G:real->real^N->real^N^N) t0`;
                   `\w. (Fq:real->real^N->real) t0 w -
                        (Bc * inv((psi:real^N->real) w pow 2) + Lam)`; `z0:real^N`]
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
                   `\w. Bc * inv((psi:real^N->real) w pow 2) + Lam`; `z0:real^N`]
           RFA_LLAP_SUB) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "Fev" (MP_TAC o SPECL [`t0:real`; `z0:real^N`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dF:real` (CONJUNCTS_THEN2 (LABEL_TAC "dF") (LABEL_TAC "ev"))) THEN
  SUBGOAL_THEN `&0 <= dF - &0` (LABEL_TAC "nn") THENL
   [MATCH_MP_TAC RFA_DERIV_NONNEG_LEFT THEN
    MAP_EVERY EXISTS_TAC
     [`\s. (Fq:real->real^N->real) s z0 - (Bc * inv((psi:real^N->real) z0 pow 2) + Lam)`;
      `t0:real`; `t0 - sigma`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      USE_THEN "bef" (MP_TAC o SPECL [`s:real`; `z0:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "eq" MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "cut" (MP_TAC o SPECL [`t0:real`; `z0:real^N`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s < t0` THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "bef" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `s:real = t0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "eq" MP_TAC THEN REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "g2") (LABEL_TAC "lp"))] THEN
  SUBGOAL_THEN `&0 <= lgrad2 ((G:real->real^N->real^N^N) t0) psi z0` ASSUME_TAC THENL
   [MATCH_MP_TAC LGRAD2_POS THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(psi:real^N->real) z0`; `llap ((G:real->real^N->real^N^N) t0) psi z0`;
                 `lgrad2 ((G:real->real^N->real^N^N) t0) psi z0`; `Bc:real`;
                 `delta:real`; `Lam:real`; `D:real`; `beta2:real`;
                 `gam:real`] RFA_SUPERSOL_ALG0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ss") THEN
  MP_TAC(ISPECL [`{z | z IN U /\ &0 < (psi:real^N->real) z}`;
                 `(G:real->real^N->real^N^N) t0`; `psi:real^N->real`; `z0:real^N`;
                 `Bc:real`; `Lam:real`] RFA_LLAP_INVSQ) THEN
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

(* ========================================================================= *)
(* Local Ricci flows from the initial time a (rfa_lfrom: local               *)
(* chart extensions below a), and continuity up to a of local curvature      *)
(* quantities (RFA_EXT_LOCAL_CONTINUOUS patched over the local extensions).  *)
(* ========================================================================= *)

let rfa_lfrom = new_definition
 `rfa_lfrom (U:real^N->bool) (a:real) (b:real) (G:real->real^N->real^N^N) <=>
    lricci_flow U a b G /\ metric_field U (G a) /\
    !y. y IN U
        ==> ?V e (FF:real^(1,N)finite_sum->real^(N,N)finite_prod).
              open V /\ y IN V /\ V SUBSET U /\ &0 < e /\
              smooth_map_on (interval(lift(a - e),lift b) PCROSS V) FF /\
              !t z. a <= t /\ t < b /\ z IN V
                    ==> FF(pastecart (lift t) z) = vectorize(G t z)`;;

let RFA_LFROM_METRIC = prove
 (`!U a b (G:real->real^N->real^N^N) t.
     rfa_lfrom U a b G /\ a <= t /\ t < b ==> metric_field U (G t)`,
  REWRITE_TAC[rfa_lfrom] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t:real = a` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`]
         LRG_FLOW_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let RFA_LFROM_QF_CONT = prove
 (`!(Qf:(real^N->real^N^N)->real^N->real) U a b (G:real->real^N->real^N^N) S.
     (!U ta tb G. lrg_lsmooth U ta tb G
                  ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                        (\z. lift(Qf (G (drop(fstcart z))) (sndcart z)))) /\
     (!G1 G2 s y. open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
                  ==> Qf G1 y = Qf G2 y) /\
     rfa_lfrom U a b G /\
     S SUBSET {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\ sndcart w IN U}
     ==> (\w. lift(Qf (G (drop(fstcart w))) (sndcart w))) continuous_on S`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Qs") (CONJUNCTS_THEN2 (LABEL_TAC "Ql")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfa_lfrom]) THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `w0:real^(1,N)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `a <= drop(fstcart(w0:real^(1,N)finite_sum)) /\ drop(fstcart w0) < b /\
                sndcart w0 IN (U:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sndcart(w0:real^(1,N)finite_sum)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` (X_CHOOSE_THEN `e:real`
    (X_CHOOSE_THEN `FF:real^(1,N)finite_sum->real^(N,N)finite_prod` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`Qf:(real^N->real^N^N)->real^N->real`; `V:real^N->bool`; `a:real`;
                 `b:real`; `e:real`; `G:real->real^N->real^N^N`;
                 `FF:real^(1,N)finite_sum->real^(N,N)finite_prod`]
         RFA_EXT_LOCAL_CONTINUOUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_LFROM_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `w0:real^(1,N)finite_sum`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {w:real^(1,N)finite_sum | sndcart w IN V}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_SNDCART];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN] THEN
  SUBGOAL_THEN `w0 IN interior {w:real^(1,N)finite_sum | sndcart w IN V}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTERIOR_OPEN; IN_ELIM_THM]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP LIM_WITHIN_INTERIOR_INTER th)]) THEN
  MATCH_MP_TAC LIM_WITHIN_SUBSET THEN
  EXISTS_TAC `{w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                   sndcart(w:real^(1,N)finite_sum) IN V}` THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_WITHIN]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `S SUBSET {w | a <= drop(fstcart w) /\ drop(fstcart w) < b /\
                               sndcart(w:real^(1,N)finite_sum) IN (U:real^N->bool)}` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[]]);;

let RFA_LFROM_SLICE_CONT = prove
 (`!(Qf:(real^N->real^N^N)->real^N->real) U a b (G:real->real^N->real^N^N) y t.
     (!U ta tb G. lrg_lsmooth U ta tb G
                  ==> smooth_map_on (interval(lift ta,lift tb) PCROSS U)
                        (\z. lift(Qf (G (drop(fstcart z))) (sndcart z)))) /\
     (!G1 G2 s y. open s /\ y IN s /\ (!z. z IN s ==> G1 z = G2 z)
                  ==> Qf G1 y = Qf G2 y) /\
     rfa_lfrom U a b G /\ y IN U /\ t < b
     ==> (\s. lift(Qf (G (drop s)) y)) continuous_on interval[lift a,lift t]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Qf:(real^N->real^N^N)->real^N->real`; `U:real^N->bool`; `a:real`;
                 `b:real`; `G:real->real^N->real^N^N`;
                 `IMAGE (\s:real^1. pastecart s (y:real^N)) (interval[lift a,lift t])`]
         RFA_LFROM_QF_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; FSTCART_PASTECART;
                SNDCART_PASTECART; IN_INTERVAL_1] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(\s. lift((Qf:(real^N->real^N^N)->real^N->real) ((G:real->real^N->real^N^N) (drop s)) y)) =
    (\w. lift(Qf (G (drop(fstcart w))) (sndcart w))) o (\s:real^1. pastecart s (y:real^N))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let RFA_LFROM_QFORM_CONT = prove
 (`!U a b (G:real->real^N->real^N^N) y t v.
     rfa_lfrom U a b G /\ y IN U /\ t < b
     ==> (\s. v dot (G s y ** v)) real_continuous_on real_interval[a,t]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON; IMAGE_LIFT_REAL_INTERVAL] THEN
  REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`\(G0:real^N->real^N^N) y. v dot (G0 y ** v)`; `U:real^N->bool`;
                 `a:real`; `b:real`; `G:real->real^N->real^N^N`; `y:real^N`; `t:real`]
         RFA_LFROM_SLICE_CONT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
    SUBGOAL_THEN
     `(\z. lift(v dot ((G':real->real^N->real^N^N) (drop(fstcart z)) (sndcart z) ** v))) =
      (\m:real^(N,N)finite_prod. lift(v dot ((matrify m:real^N^N) ** v))) o
      (\z. vectorize(G' (drop(fstcart z)) (sndcart z)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; MATRIFY_VECTORIZE]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_REWRITE_TAC[LRG_LINEAR_MATRIFY_DOT];
    SIMP_TAC[]]);;

let RFA_LFROM_GAMMA_CONT = prove
 (`!U a b (G:real->real^N->real^N^N) y t u v.
     rfa_lfrom U a b G /\ y IN U /\ t < b
     ==> (\s. christoffel (G (drop s)) y u v) continuous_on interval[lift a,lift t]`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\(G0:real^N->real^N^N) y. (christoffel G0 y u v)$k`; `U:real^N->bool`;
                 `a:real`; `b:real`; `G:real->real^N->real^N^N`; `y:real^N`; `t:real`]
         RFA_LFROM_SLICE_CONT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(\z. lift((christoffel ((G':real->real^N->real^N^N) (drop(fstcart z))) (sndcart z)
                             u v)$k)) =
      (\x:real^N. lift(x$k)) o
      (\z. christoffel (G' (drop(fstcart z))) (sndcart z) u v)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[LINEAR_LIFT_COMPONENT; LRG_LSMOOTH_CHRISTOFFEL];
    REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN ASM_MESON_TAC[]]);;

let RFA_LFROM_BERN_CONT = prove
 (`!U a b (G:real->real^N->real^N^N) Kc tau Bq m.
     rfa_lfrom U a b G /\ Kc SUBSET U /\ tau < b
     ==> (\w. lift((Bq + lrm_deriv_norm2 (m - 1) (G (drop(fstcart w))) (sndcart w)) *
                   lrm_deriv_norm2 m (G (drop(fstcart w))) (sndcart w)))
         continuous_on (interval[lift a,lift tau] PCROSS Kc)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\(G0:real^N->real^N^N) y.
                    (Bq + lrm_deriv_norm2 (m - 1) G0 y) * lrm_deriv_norm2 m G0 y`;
                 `U:real^N->bool`; `a:real`; `b:real`; `G:real->real^N->real^N^N`;
                 `interval[lift a,lift tau] PCROSS (Kc:real^N->bool)`]
         RFA_LFROM_QF_CONT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LRG_LSMOOTH_BASIC) THEN
    MATCH_MP_TAC RFA_BERN_QUANT_SMOOTH THEN ASM_SIMP_TAC[RFA_LSMOOTH_LRM_NORM2];
    REPEAT STRIP_TAC THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_INTERVAL_1;
                IN_ELIM_THM; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Metric comparison and Christoffel change from the initial                 *)
(* time (continuity at a from rfa_lfrom), and the metric lemma of the local  *)
(* step at the initial time.                                                 *)
(* ========================================================================= *)

let RFA_LMETRIC_EQUIV0 = prove
 (`!U a b (G:real->real^N->real^N^N) y t Kr.
     rfa_lfrom U a b G /\ a <= t /\ t < b /\ y IN U /\ &0 <= Kr /\
     (!s v. a <= s /\ s <= t ==> abs(lricci (G s) y v v) <= Kr * (v dot (G s y ** v)))
     ==> !v. exp(--(&2 * Kr * (t - a))) * (v dot (G a y ** v)) <= v dot (G t y ** v) /\
             v dot (G t y ** v) <= exp(&2 * Kr * (t - a)) * (v dot (G a y ** v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfa_lfrom]) THEN
  ASM_CASES_TAC `t:real = a` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s. v dot ((G:real->real^N->real^N^N) s y ** v)`;
                 `\s. --(&2) * lricci ((G:real->real^N->real^N^N) s) y v v`;
                 `&2 * Kr`; `a:real`; `t:real`] RFA_GRONWALL_2SIDED) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC RFA_LFROM_QFORM_CONT THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `b:real`] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_LQFORM_DERIV THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let RFA_GAMMA_CHANGE0 = prove
 (`!U a b (G:real->real^N->real^N^N) t1 y v Lm A B.
     rfa_lfrom U a b G /\ a < t1 /\ t1 < b /\ y IN U /\
     &0 <= Lm /\
     (!s x. a < s /\ s < t1
            ==> norm x pow 2 <= Lm * (x dot (G s y ** x)) /\
                x dot (G s y ** x) <= Lm * norm x pow 2) /\
     (!s. a < s /\ s < t1
          ==> sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 (G s) y) <=
              A * inv(sqrt(s - a)) + B)
     ==> norm(christoffel (G t1) y v v - christoffel (G a) y v v) <=
         ((&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) * norm v pow 2) *
         (&2 * A * sqrt(t1 - a) + B * (t1 - a))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfa_lfrom]) THEN
  ABBREV_TAC `Cg = (&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) * norm(v:real^N) pow 2` THEN
  SUBGOAL_THEN `&0 <= Cg` ASSUME_TAC THENL
   [EXPAND_TAC "Cg" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE; REAL_LE_POW_2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real`; `B:real`; `a:real`; `t1:real`] RFA_SQRT_GROWTH) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. christoffel ((G:real->real^N->real^N^N) (drop s)) y v v`;
                 `\s. ldgamma (G:real->real^N->real^N^N) s y v v`;
                 `\s. Cg * (&2 * A * sqrt(s - a) + B * (s - a))`;
                 `\s. Cg * (A * inv(sqrt(s - a)) + B)`; `a:real`; `t1:real`]
         RFA_VEC_DERIV_COMPARE) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_LFROM_GAMMA_CONT THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `b:real`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC RFA_GAMMA_VDERIV THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_ATREAL THEN ASM_SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm) *
                  sqrt(&(dimindex(:N)) *
                       lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) s) y) *
                  norm(v:real^N) * norm v` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RFA_DGAMMA_BOUND THEN
        MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `a:real`; `b:real`] THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm) *
        sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 ((G:real->real^N->real^N^N) s) y) *
        norm(v:real^N) * norm v =
        Cg * sqrt(&(dimindex(:N)) * lrm_deriv_norm2 1 (G s) y)`
      SUBST1_TAC THENL
       [EXPAND_TAC "Cg" THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; SQRT_0; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_SUB_RZERO]);;

let RFA_SLOC_METRIC0 = prove
 (`!a b (G:real->real^N->real^N^N) t1 Tm rho K A0.
     rfa_lfrom (ball(vec 0,rho)) a b G /\ a <= t1 /\ t1 < b /\ t1 - a <= Tm /\
     rfa_expc (G a) rho K /\ &0 <= A0 /\
     (!s z. a <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0)
     ==> !s z. a <= s /\ s <= t1 /\ norm z < rho
               ==> !x. x dot (G a z ** x) <=
                     exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm) *
                     (x dot (G s z ** x)) /\
                     norm x pow 2 <=
                     (&2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm)) *
                     (x dot (G s z ** x)) /\
                     x dot (G s z ** x) <=
                     (&2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm)) *
                     norm x pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfa_lfrom]) THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `z:real^N`] THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Kr = &(dimindex(:N)) * sqrt A0` THEN
  SUBGOAL_THEN `&0 <= Kr` ASSUME_TAC THENL
   [EXPAND_TAC "Kr" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `z:real^N`; `s:real`;
                 `Kr:real`] RFA_LMETRIC_EQUIV0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s':real`; `v:real^N`] THEN STRIP_TAC THEN
    EXPAND_TAC "Kr" THEN MATCH_MP_TAC RFA_LRIC_BOUND THEN
    EXISTS_TAC `ball(vec 0:real^N,rho)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFA_LFROM_METRIC THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^N`; `x:real^N`] o CONJUNCT1 o
    GEN_REWRITE_RULE I [rfa_expc]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `E = exp(&2 * Kr * Tm)` THEN
  ABBREV_TAC `e1 = exp(&2 * Kr * (s - a))` THEN
  SUBGOAL_THEN `&0 < e1 /\ e1 <= E /\ e1 * exp(--(&2 * Kr * (s - a))) = &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "E"] THEN
    REWRITE_TAC[REAL_EXP_POS_LT; REAL_EXP_MONO_LE; REAL_EXP_NEG_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `P0 = (x:real^N) dot ((G:real->real^N->real^N^N) a z ** x)` THEN
  ABBREV_TAC `P1 = (x:real^N) dot ((G:real->real^N->real^N^N) s z ** x)` THEN
  ABBREV_TAC `em = exp(--(&2 * Kr * (s - a)))` THEN
  SUBGOAL_THEN `&0 <= P0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2) * ((x:real^N) dot x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[DOT_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `P0 <= e1 * P1` ASSUME_TAC THENL
   [SUBGOAL_THEN `e1 * em * P0 <= e1 * P1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `em * P0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "em" THEN REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 * P1 <= E * P1 /\ e1 * P0 <= E * P0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `E * P0 <= E * (&2 * ((x:real^N) dot x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_POW_2] THEN
  UNDISCH_TAC `E * P0 <= E * (&2 * ((x:real^N) dot x))` THEN
  UNDISCH_TAC `P1 <= e1 * P0` THEN
  UNDISCH_TAC `inv(&2) * ((x:real^N) dot x) <= P0` THEN
  UNDISCH_TAC `e1 * P1 <= E * P1` THEN UNDISCH_TAC `e1 * P0 <= E * P0` THEN
  UNDISCH_TAC `P0 <= e1 * P1` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REAL_ARITH_TAC);;

let RFA_SLOC_CUT0 = prove
 (`!a b (G:real->real^N->real^N^N) t0 t1 Tm rho K A0 C1 C2 Dg z.
     rfa_lfrom (ball(vec 0,rho)) a b G /\ a <= t0 /\ t0 <= t1 /\ t1 - a <= Tm /\
     t1 < b /\ &0 < rho /\ &0 <= K /\ rfa_expc (G a) rho K /\ &0 <= A0 /\
     (!s z. a <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0) /\
     norm z < rho /\
     abs(real_derivative (rfa_prof (rho / &4) (rho / &2)) (norm z)) <= C1 /\
     abs(real_derivative (real_derivative (rfa_prof (rho / &4) (rho / &2)))
                         (norm z)) <= C2 /\
     &0 <= Dg /\
     (!v. rfa_prof (rho / &4) (rho / &2) (norm z) *
          norm(christoffel (G t0) z v v - christoffel (G a) z v v) <=
          Dg * norm v pow 2)
     ==> lgrad2 (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z <=
         C1 pow 2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm) *
         &(dimindex(:N)) /\
         --(rfa_prof (rho / &4) (rho / &2) (norm z) *
            llap (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z) <=
         ((C2 + C1 * (inv(rho / &4) + K * rho)) *
          exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm) +
          C1 * Dg * (&2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm))) *
         &(dimindex(:N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) a) /\
    metric_field (ball(vec 0,rho)) (G t0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_LFROM_METRIC THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(G:real->real^N->real^N^N) a z ** z = z` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfa_expc]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E = exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm)` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `t1:real`; `Tm:real`;
                 `rho:real`; `K:real`; `A0:real`] RFA_SLOC_METRIC0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`t0:real`; `z:real^N`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(LABEL_TAC "met")] THEN
  SUBGOAL_THEN `&0 < rho / &4 /\ rho / &4 < rho / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_CUT_GRAD THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`;
                          `(G:real->real^N->real^N^N) a`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_CUT_LAP THEN
  MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`;
                        `(G:real->real^N->real^N^N) a`] THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC RFA_EXPC_HESS_ABS THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`; `rho:real`] THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let RFA_SLOC_DG_HI0 = prove
 (`!a b (G:real->real^N->real^N^N) t0 t1 Tm rho K A0 A1 Lm z.
     rfa_lfrom (ball(vec 0,rho)) a b G /\ a < t0 /\ t0 <= t1 /\ t1 - a <= Tm /\
     t1 < b /\ &0 < rho /\ rfa_expc (G a) rho K /\ &0 <= A0 /\ &0 <= A1 /\
     (!s z. a <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0) /\
     (!s z. a <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 1 (G s) z <= A1) /\
     Lm = &2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm) /\
     norm z < rho
     ==> !v. rfa_prof (rho / &4) (rho / &2) (norm z) *
             norm(christoffel (G t0) z v v - christoffel (G a) z v v) <=
             ((&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) *
              sqrt(&(dimindex(:N)) * A1) * Tm) * norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lm` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `t1:real`; `Tm:real`;
                 `rho:real`; `K:real`; `A0:real`] RFA_SLOC_METRIC0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "met") THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t0:real`; `z:real^N`;
                 `v:real^N`; `Lm:real`; `&0`; `sqrt(&(dimindex(:N)) * A1)`]
         RFA_GAMMA_CHANGE0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^N`] THEN STRIP_TAC THEN
      USE_THEN "met" (MP_TAC o SPECL [`s:real`; `z:real^N`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  ABBREV_TAC `nG = norm(christoffel ((G:real->real^N->real^N^N) t0) z v v -
                        christoffel (G a) z v v)` THEN
  ABBREV_TAC `ps = rfa_prof (rho / &4) (rho / &2) (norm(z:real^N))` THEN
  ABBREV_TAC `sA = sqrt(&(dimindex(:N)) * A1)` THEN
  ABBREV_TAC `nv = norm(v:real^N) pow 2` THEN
  DISCH_TAC THEN
  ABBREV_TAC `Cg = &3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)` THEN
  SUBGOAL_THEN `&0 <= ps /\ ps <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ps" THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Cg /\ &0 <= sA /\ &0 <= nv /\ &0 <= nG` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Cg"; "sA"; "nv"; "nG"] THEN
    REWRITE_TAC[NORM_POS_LE; REAL_LE_POW_2] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ps * nG <= nG` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cg * nv * sA) * (t0 - a) <= (Cg * nv * sA) * Tm` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(Cg * nv * sA) * (t0 - a) <= (Cg * nv * sA) * Tm` THEN
  UNDISCH_TAC `ps * nG <= nG` THEN
  UNDISCH_TAC `nG <= (Cg * nv) * sA * (t0 - a)` THEN
  REAL_ARITH_TAC);;

let RFA_BOOT_RATE0 = prove
 (`!n B Bc Lam ps r0 r1.
     &0 <= n /\ &0 < B /\ &0 < Bc /\ &0 <= Lam /\ &0 < ps /\ &0 <= r0 /\ &0 <= r1 /\
     (B + r0) * r1 <= Bc * inv(ps pow 2) + Lam
     ==> sqrt(n * r1) <= sqrt(n / B) * (sqrt Bc * inv ps + sqrt Lam)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `H = Bc * inv(ps pow 2) + Lam` THEN
  SUBGOAL_THEN `B * r1 <= H` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B + r0) * r1` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n * r1 <= n / B * H` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(n / B) * sqrt H` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXPAND_TAC "H" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(Bc * inv(ps pow 2)) + sqrt Lam + sqrt(&0)` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
    MATCH_MP_TAC RFA_SQRT_ADD3_LE THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC REAL_POW_LE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[SQRT_0; REAL_ADD_RID; SQRT_MUL; SQRT_INV] THEN
    ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE; REAL_LE_REFL]]);;

let RFA_SLOC_DG_BOOT0 = prove
 (`!a b (G:real->real^N->real^N^N) t0 t1 Tm rho K A0 Lm B Bc Lam z.
     rfa_lfrom (ball(vec 0,rho)) a b G /\ a < t0 /\ t0 <= t1 /\ t1 - a <= Tm /\
     t1 < b /\ &0 < rho /\ rfa_expc (G a) rho K /\ &0 <= A0 /\
     (!s z. a <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 (G s) z <= A0) /\
     Lm = &2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm) /\
     &0 < B /\ &0 < Bc /\ &0 <= Lam /\ norm z < rho /\
     &0 < rfa_prof (rho / &4) (rho / &2) (norm z) /\
     (!s. a <= s /\ s <= t0
          ==> (B + lrm_deriv_norm2 0 (G s) z) * lrm_deriv_norm2 1 (G s) z <=
              Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) + Lam)
     ==> !v. rfa_prof (rho / &4) (rho / &2) (norm z) *
             norm(christoffel (G t0) z v v - christoffel (G a) z v v) <=
             ((&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)) *
              (sqrt(&(dimindex(:N)) / B) * (sqrt Bc + sqrt Lam) * Tm)) *
             norm v pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^N` THEN
  SUBGOAL_THEN `(z:real^N) IN ball(vec 0,rho)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lm` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `t1:real`; `Tm:real`;
                 `rho:real`; `K:real`; `A0:real`] RFA_SLOC_METRIC0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "met") THEN
  ABBREV_TAC `ps = rfa_prof (rho / &4) (rho / &2) (norm(z:real^N))` THEN
  SUBGOAL_THEN `ps <= &1` ASSUME_TAC THENL
   [EXPAND_TAC "ps" THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                 `G:real->real^N->real^N^N`; `t0:real`; `z:real^N`;
                 `v:real^N`; `Lm:real`; `&0`;
                 `sqrt(&(dimindex(:N)) / B) * (sqrt Bc * inv ps + sqrt Lam)`]
         RFA_GAMMA_CHANGE0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `x:real^N`] THEN STRIP_TAC THEN
      USE_THEN "met" (MP_TAC o SPECL [`s:real`; `z:real^N`]) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN SIMP_TAC[];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) s)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC RFA_LFROM_METRIC THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
      MATCH_MP_TAC RFA_BOOT_RATE0 THEN
      EXISTS_TAC `lrm_deriv_norm2 0 ((G:real->real^N->real^N^N) s) z` THEN
      ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= &3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; SQRT_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sqrt(&(dimindex(:N)) / B) /\ &0 <= sqrt Bc /\ &0 <= sqrt Lam`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
    TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  UNDISCH_TAC `Lm = &2 * exp(&2 * (&(dimindex(:N)) * sqrt A0) * Tm)` THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(SPECL [`ps:real`;
                `norm(christoffel ((G:real->real^N->real^N^N) t0) z v v -
                      christoffel (G a) z v v)`;
                `&3 * &(dimindex(:N)) * Lm * (Lm * sqrt Lm)`; `norm(v:real^N) pow 2`;
                `&0`; `sqrt(&(dimindex(:N)) / B)`; `sqrt Bc`; `sqrt Lam`;
                `t0 - a:real`; `Tm:real`; `&0`; `&0`] RFA_BOOT_ALG) THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* The barrier argument from the initial time a: the Bernstein               *)
(* quantity stays below Bc / psi^2 + Lam on [a,t1] when it starts below it.  *)
(* ========================================================================= *)

let RFA_SLOC_BARRIER_APPLY0 = prove
 (`!m (A:num->real) Bq D a b (G:real->real^N->real^N^N) t1 rho delta Bc Lam
    beta2 gam.
     1 <= m /\ &0 < Bq /\ &0 < rho /\ &0 <= A(m - 1) /\
     (!U a b (G:real->real^N->real^N^N) t y.
        lricci_flow U a b G /\ a < t /\ t < b /\ y IN U /\
        (!i. i < m ==> lrm_deriv_norm2 i (G t) y <= A i)
        ==> ?dF. ((\s. (Bq + lrm_deriv_norm2 (m - 1) (G s) y) *
                       lrm_deriv_norm2 m (G s) y) has_real_derivative dF) (atreal t) /\
                 dF <= llap (G t) (\z. (Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                                       lrm_deriv_norm2 m (G t) z) y -
                       ((Bq + lrm_deriv_norm2 (m - 1) (G t) y) *
                        lrm_deriv_norm2 m (G t) y) pow 2 /
                       (&2 * (Bq + A(m - 1)) pow 2) + D) /\
     delta = inv(&2 * (Bq + A(m - 1)) pow 2) /\
     rfa_lfrom (ball(vec 0,rho)) a b G /\ a < t1 /\ t1 < b /\
     (!i s z. i < m /\ a <= s /\ s <= t1 /\ norm z < rho
              ==> lrm_deriv_norm2 i (G s) z <= A i) /\
     &0 < Bc /\ &0 <= Lam /\ D <= delta * Lam pow 2 /\
     &2 * gam + &6 * beta2 < delta * Bc /\
     (!z. z IN ball(vec 0,rho) /\ &0 < rfa_prof (rho / &4) (rho / &2) (norm z)
          ==> (Bq + lrm_deriv_norm2 (m - 1) (G a) z) * lrm_deriv_norm2 m (G a) z <
              Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) + Lam) /\
     (!t0 z. a < t0 /\ t0 <= t1 /\ z IN ball(vec 0,rho) /\
             &0 < rfa_prof (rho / &4) (rho / &2) (norm z) /\
             (!t. a <= t /\ t <= t0
                  ==> (Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                      lrm_deriv_norm2 m (G t) z <=
                      Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) + Lam)
             ==> lgrad2 (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z <=
                 beta2 /\
                 --(rfa_prof (rho / &4) (rho / &2) (norm z) *
                    llap (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z) <=
                 gam)
     ==> lrm_deriv_norm2 m (G t1) (vec 0) <= (Bc + Lam) / Bq`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "bern")
   (CONJUNCTS_THEN2 (LABEL_TAC "deq") STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
   [USE_THEN "deq" SUBST1_TAC THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!X. X pow 2 / (&2 * (Bq + (A:num->real)(m - 1)) pow 2) = delta * X pow 2`
  (LABEL_TAC "dq") THENL
   [USE_THEN "deq" SUBST1_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "deq" (K ALL_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfa_lfrom]) THEN
  SUBGOAL_THEN
   `!t. a < t /\ t < b
        ==> metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) t)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`;
                   `G:real->real^N->real^N^N`] LRG_FLOW_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^N,rho / &2) SUBSET ball(vec 0,rho)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (ball(vec 0:real^N,rho))
      (\z. lift(rfa_prof (rho / &4) (rho / &2) (norm z)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_BUMP_SMOOTH_ON THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN ball(vec 0,rho) ==> &0 <= rfa_prof (rho / &4) (rho / &2) (norm z)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN ball(vec 0,rho) /\ ~(z IN cball(vec 0,rho / &2))
               ==> rfa_prof (rho / &4) (rho / &2) (norm z) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_CBALL_0] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `norm(z:real^N)`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NORM] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. lift((Bq + lrm_deriv_norm2 (m - 1)
                  ((G:real->real^N->real^N^N) (drop(fstcart w))) (sndcart w)) *
              lrm_deriv_norm2 m (G (drop(fstcart w))) (sndcart w)))
    continuous_on (interval[lift a,lift t1] PCROSS cball(vec 0,rho / &2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_LFROM_BERN_CONT THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. a < t /\ t <= t1
        ==> smooth_map_on (ball(vec 0:real^N,rho))
              (\z. lift((Bq + lrm_deriv_norm2 (m - 1)
                               ((G:real->real^N->real^N^N) t) z) *
                        lrm_deriv_norm2 m (G t) z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `metric_field (ball(vec 0:real^N,rho)) ((G:real->real^N->real^N^N) t)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RFA_BERN_QUANT_SMOOTH THEN
    ASM_SIMP_TAC[OPEN_BALL; RFA_RMD_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t z. a < t /\ t <= t1 /\ z IN ball(vec 0,rho)
          ==> ?dF. ((\s. (Bq + lrm_deriv_norm2 (m - 1)
                                 ((G:real->real^N->real^N^N) s) z) *
                         lrm_deriv_norm2 m (G s) z) has_real_derivative dF)
                   (atreal t) /\
                   dF <= llap (G t) (\z. (Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                                         lrm_deriv_norm2 m (G t) z) z -
                         delta * ((Bq + lrm_deriv_norm2 (m - 1) (G t) z) *
                                  lrm_deriv_norm2 m (G t) z) pow 2 + D`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a < t /\ t < b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "dq" (fun th -> REWRITE_TAC[GSYM th]) THEN
    USE_THEN "bern" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^N,rho)`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(vec 0:real^N,rho)`; `cball(vec 0:real^N,rho / &2)`;
                 `G:real->real^N->real^N^N`;
                 `\t z. (Bq + lrm_deriv_norm2 (m - 1)
                                ((G:real->real^N->real^N^N) t) z) *
                        lrm_deriv_norm2 m (G t) z`;
                 `\w:real^N. rfa_prof (rho / &4) (rho / &2) (norm w)`;
                 `a:real`; `b:real`; `a:real`; `t1:real`; `delta:real`;
                 `D:real`; `Bc:real`; `Lam:real`; `beta2:real`; `gam:real`]
         RFA_LOCAL_BARRIER0) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL; COMPACT_CBALL; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t1:real`; `vec 0:real^N`]) THEN
  SUBGOAL_THEN `rfa_prof (rho / &4) (rho / &2) (norm(vec 0:real^N)) = &1`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_0] THEN
    MP_TAC(ISPECL [`rho / &4`; `rho / &2`; `&0`] RFA_PROF_VALUES) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_0] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LE_REFL; REAL_LT_01] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_INV_1; REAL_MUL_RID] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t1) (vec 0) /\
    &0 <= lrm_deriv_norm2 m ((G:real->real^N->real^N^N) t1) (vec 0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_RMD_POS THEN
    EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r0 = lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t1) (vec 0)` THEN
  ABBREV_TAC `r1 = lrm_deriv_norm2 m ((G:real->real^N->real^N^N) t1) (vec 0)` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= r0 * r1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(Bq + r0) * r1 < Bc + Lam` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The local estimate of order m >= 1 at the centre, from the                *)
(* initial time a with initial bound A1 on |nabla^m Rm|^2 (no blow-up at a). *)
(* ========================================================================= *)

let RFA_SLOC_STEP0 = prove
 (`!m (A:num->real) A1 K rho tau.
     1 <= m /\ (!i. &0 <= A i) /\ &0 <= A1 /\ &0 < rho /\ &0 <= K /\ &0 < tau
     ==> ?C. !a b (G:real->real^N->real^N^N) t1.
               rfa_lfrom (ball(vec 0,rho)) a b G /\ a < t1 /\ t1 < b /\ t1 - a <= tau /\
               rfa_expc (G a) rho K /\
               (!i s z. i < m /\ a <= s /\ s <= t1 /\ norm z < rho
                        ==> lrm_deriv_norm2 i (G s) z <= A i) /\
               (!z. norm z < rho ==> lrm_deriv_norm2 m (G a) z <= A1)
               ==> lrm_deriv_norm2 m (G t1) (vec 0) <= C`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Bq = &8 * (A:num->real)(m - 1) + &1` THEN
  SUBGOAL_THEN `&0 < Bq /\ &8 * (A:num->real)(m - 1) <= Bq /\ &0 <= A(m - 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Bq" THEN FIRST_ASSUM(MP_TAC o SPEC `m - 1`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `A:num->real`; `Bq:real`] RFA_BERN_FLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` (LABEL_TAC "bern")) THEN
  ABBREV_TAC `delta = inv(&2 * (Bq + (A:num->real)(m - 1)) pow 2)` THEN
  SUBGOAL_THEN `&0 < delta` ASSUME_TAC THENL
   [EXPAND_TAC "delta" THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = max (sqrt(abs D / delta)) ((Bq + (A:num->real)(m - 1)) * A1 + &1)` THEN
  SUBGOAL_THEN `&0 <= Lam /\ D <= delta * Lam pow 2 /\
                (Bq + (A:num->real)(m - 1)) * A1 < Lam` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= abs D / delta` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(abs D / delta) /\ sqrt(abs D / delta) <= Lam /\
                  (Bq + (A:num->real)(m - 1)) * A1 + &1 <= Lam` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LE] THEN EXPAND_TAC "Lam" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `delta * sqrt(abs D / delta) pow 2` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[SQRT_POW_2; REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho / &4`; `rho / &2`; `rho:real`] RFA_PROF_DBOUNDS) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (X_CHOOSE_THEN `C2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd"))))) THEN
  ABBREV_TAC `E = exp(&2 * (&(dimindex(:N)) * sqrt((A:num->real) 0)) * tau)` THEN
  ABBREV_TAC `Cg = &3 * &(dimindex(:N)) * (&2 * E) * ((&2 * E) * sqrt(&2 * E))` THEN
  ABBREV_TAC
   `dq0 = if m = 1
          then sqrt(&(dimindex(:N)) / Bq) * sqrt Lam * tau
          else sqrt(&(dimindex(:N)) * (A:num->real) 1) * tau` THEN
  ABBREV_TAC `dq1 = if m = 1 then sqrt(&(dimindex(:N)) / Bq) * tau else &0` THEN
  ABBREV_TAC `beta2 = C1 pow 2 * E * &(dimindex(:N))` THEN
  ABBREV_TAC `g0 = (C2 + C1 * (inv(rho / &4) + K * rho)) * E` THEN
  SUBGOAL_THEN
   `&0 <= E /\ &0 <= Cg /\ &0 <= dq0 /\ &0 <= dq1 /\ &0 <= beta2 /\ &0 <= g0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 <= sqrt(&(dimindex(:N)) / (Bq * delta)) /\
      &0 <= sqrt(&(dimindex(:N)) / Bq) /\ &0 <= sqrt tau /\ &0 <= sqrt Lam /\
      &0 <= sqrt(&(dimindex(:N)) * (A:num->real) 1) /\ &0 <= sqrt(&2 * E)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN
      TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Cg" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "dq0" THEN COND_CASES_TAC THEN
      REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
             CONJ_TAC) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "dq1" THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "beta2" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
      EXPAND_TAC "g0" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`&2 * (g0 + C1 * (Cg * dq0) * (&2 * E)) * &(dimindex(:N)) + &6 * beta2`;
    `&2 * (C1 * (Cg * dq1) * (&2 * E)) * &(dimindex(:N))`; `delta:real`]
   RFA_BC_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
           CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Bc:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(Bc + Lam) / Bq` THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `G:real->real^N->real^N^N`; `t1:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `gam = (g0 + C1 * (Cg * (dq0 + dq1 * sqrt Bc)) * (&2 * E)) *
                    &(dimindex(:N))` THEN
  SUBGOAL_THEN `&2 * gam + &6 * beta2 < delta * Bc` ASSUME_TAC THENL
   [EXPAND_TAC "gam" THEN
    UNDISCH_TAC
     `(&2 * (g0 + C1 * (Cg * dq0) * (&2 * E)) * &(dimindex(:N)) + &6 * beta2) +
      (&2 * (C1 * (Cg * dq1) * (&2 * E)) * &(dimindex(:N))) * sqrt Bc < delta * Bc` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0 z. a < t0 /\ t0 <= t1 /\ z IN ball(vec 0,rho) /\
           &0 < rfa_prof (rho / &4) (rho / &2) (norm z) /\
           (!t. a <= t /\ t <= t0
                ==> (Bq + lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) t) z) *
                    lrm_deriv_norm2 m (G t) z <=
                    Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) + Lam)
           ==> lgrad2 (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z <= beta2 /\
               --(rfa_prof (rho / &4) (rho / &2) (norm z) *
                  llap (G t0) (\w. rfa_prof (rho / &4) (rho / &2) (norm w)) z) <= gam`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`t0:real`; `z:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FH"))))) THEN
    SUBGOAL_THEN `norm(z:real^N) < rho` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_BALL_0]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!s z. a <= s /\ s <= t1 /\ norm z < rho
            ==> lrm_deriv_norm2 0 ((G:real->real^N->real^N^N) s) z <= (A:num->real) 0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!v. rfa_prof (rho / &4) (rho / &2) (norm z) *
          norm(christoffel ((G:real->real^N->real^N^N) t0) z v v -
               christoffel (G a) z v v) <=
          (Cg * (dq0 + dq1 * sqrt Bc)) * norm v pow 2`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `m = 1` THENL
       [SUBGOAL_THEN
         `dq0 + dq1 * sqrt Bc =
          sqrt(&(dimindex(:N)) / Bq) * (sqrt Bc + sqrt Lam) * tau`
        SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["dq0"; "dq1"] THEN REWRITE_TAC[ASSUME `m = 1`] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        REMOVE_THEN "FH" MP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`;
                       `t0:real`; `t1:real`; `tau:real`; `rho:real`; `K:real`;
                       `(A:num->real) 0`; `&2 * E`; `Bq:real`;
                       `Bc:real`; `Lam:real`; `z:real^N`] RFA_SLOC_DG_BOOT0) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `dq0 + dq1 * sqrt Bc = sqrt(&(dimindex(:N)) * (A:num->real) 1) * tau`
        SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["dq0"; "dq1"] THEN REWRITE_TAC[ASSUME `~(m = 1)`] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`;
                       `t0:real`; `t1:real`; `tau:real`; `rho:real`; `K:real`;
                       `(A:num->real) 0`; `(A:num->real) 1`; `&2 * E`; `z:real^N`]
               RFA_SLOC_DG_HI0) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(real_derivative (rfa_prof (rho / &4) (rho / &2)) (norm(z:real^N))) <= C1 /\
      abs(real_derivative (real_derivative (rfa_prof (rho / &4) (rho / &2)))
                          (norm z)) <= C2`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "pd" MATCH_MP_TAC THEN REWRITE_TAC[REAL_ABS_NORM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Cg * (dq0 + dq1 * sqrt Bc) /\ a <= t0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real`; `b:real`; `G:real->real^N->real^N^N`;
                   `t0:real`; `t1:real`; `tau:real`; `rho:real`; `K:real`;
                   `(A:num->real) 0`; `C1:real`; `C2:real`;
                   `Cg * (dq0 + dq1 * sqrt Bc)`; `z:real^N`] RFA_SLOC_CUT0) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball(vec 0,rho) /\ &0 < rfa_prof (rho / &4) (rho / &2) (norm z)
        ==> (Bq + lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) a) z) *
            lrm_deriv_norm2 m (G a) z <
            Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm z) pow 2) + Lam`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(z:real^N) < rho` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_BALL_0]; ALL_TAC] THEN
    SUBGOAL_THEN `metric_field (ball(vec 0,rho)) ((G:real->real^N->real^N^N) a)`
    ASSUME_TAC THENL [ASM_MESON_TAC[rfa_lfrom]; ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= lrm_deriv_norm2 (m - 1) ((G:real->real^N->real^N^N) a) z /\
      &0 <= lrm_deriv_norm2 m ((G:real->real^N->real^N^N) a) z /\
      lrm_deriv_norm2 (m - 1) (G a) z <= (A:num->real)(m - 1) /\
      lrm_deriv_norm2 m (G a) z <= A1`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC RFA_RMD_POS THEN EXISTS_TAC `ball(vec 0:real^N,rho)` THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Bc * inv(rfa_prof (rho / &4) (rho / &2) (norm(z:real^N)) pow 2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                                                REAL_LE_POW_2];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(Bq + (A:num->real)(m - 1)) * A1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC RFA_SLOC_BARRIER_APPLY0 THEN
  MAP_EVERY EXISTS_TAC [`A:num->real`; `D:real`; `a:real`; `b:real`; `rho:real`;
                        `delta:real`; `beta2:real`; `gam:real`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The exp pullback of a Ricci flow from the initial time is a               *)
(* local Ricci flow from that time (rfa_lfrom), and the derivative norms are *)
(* preserved at every time where the metric is Riemannian.                   *)
(* ========================================================================= *)

(* The joint smoothness part of LRICCI_FLOW_PULLBACK, for any time interval  *)
(* and any smooth map h of U' into U.  PDM_MPULLBACK_SMOOTH_ST of the unit   *)
(* pc_pde_mloc has the same content, but that unit (PDE layer) is outside    *)
(* the load closure of this unit.                                            *)

let RFA_PULLBACK_FAMILY_SMOOTH = prove
 (`!a1 b1 U U' (h:real^N->real^N) (Gf:real->real^N->real^N^N).
     open U /\ open U' /\ smooth_map_on U' h /\ IMAGE h U' SUBSET U /\
     smooth_map_on (interval(lift a1,lift b1) PCROSS U)
       (\z. (vectorize:real^N^N->real^(N,N)finite_prod) (Gf (drop(fstcart z)) (sndcart z)))
     ==> smooth_map_on (interval(lift a1,lift b1) PCROSS U')
           (\z. (vectorize:real^N^N->real^(N,N)finite_prod)
                (mpullback h (Gf (drop(fstcart z))) (sndcart z)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. vectorize(mpullback (h:real^N->real^N)
                    ((Gf:real->real^N->real^N^N) (drop(fstcart z))) (sndcart z))) =
    (vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z. transp(matrix(frechet_derivative h (at (sndcart z)))) **
         Gf (drop(fstcart z)) (h(sndcart z)) **
         matrix(frechet_derivative h (at (sndcart z))))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; mpullback]; ALL_TAC] THEN
  SUBGOAL_THEN `open(interval(lift a1,lift b1) PCROSS (U':real^N->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on (interval(lift a1,lift b1) PCROSS (U':real^N->bool))
      ((vectorize:real^N^N->real^(N,N)finite_prod) o
       (\z. matrix(frechet_derivative (h:real^N->real^N) (at (sndcart z)))))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(vectorize:real^N^N->real^(N,N)finite_prod) o
      (\z. matrix(frechet_derivative (h:real^N->real^N) (at (sndcart z)))) =
      (vectorize o (\x. matrix(frechet_derivative h (at x)))) o
      (sndcart:real^(1,N)finite_sum->real^N)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[LRG_SMOOTH_JACOBIAN; LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_SIMP_TAC[LRG_SMOOTH_TRANSP] THEN
  MATCH_MP_TAC LRG_SMOOTH_MATMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(vectorize:real^N^N->real^(N,N)finite_prod) o
    (\z. (Gf:real->real^N->real^N^N) (drop(fstcart z))
                                     ((h:real^N->real^N) (sndcart z))) =
    (\z. vectorize(Gf (drop(fstcart z)) (sndcart z))) o
    (\z:real^(1,N)finite_sum. pastecart (fstcart z) (h(sndcart z)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `interval(lift a1,lift b1) PCROSS (U:real^N->bool)` THEN
  ASM_SIMP_TAC[OPEN_PCROSS; OPEN_INTERVAL] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_PASTECART_OPEN THEN
    ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_FSTCART] THEN
    SUBGOAL_THEN
     `(\z:real^(1,N)finite_sum. (h:real^N->real^N) (sndcart z)) = h o sndcart`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `U':real^N->bool` THEN
    ASM_SIMP_TAC[LRG_SMOOTH_LINEAR; LINEAR_SNDCART] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; SNDCART_PASTECART] THEN
    SIMP_TAC[]]);;

(* The exp pullback flow with the base time sg anywhere the metric is        *)
(* Riemannian (the copies in pc_rfa_slmfd need a < sg < b).                  *)

let RFA_EXPFLOW_LRICCI_GEN = prove
 (`!top atlas (g:real->A->real^N^N) a b sg (p:A) (E:real^N^N) rho.
     hausdorff_space top /\ ricci_flow_on (top,atlas) a b g /\
     riemannian_metric atlas (g sg) /\
     p IN topspace top /\ mfd_orthonormal_frame (g sg) p E /\
     mfd_tball (g sg) p rho SUBSET mfd_exp_dom (top,atlas) (g sg) p /\
     metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) (g sg) p E)
     ==> lricci_flow (ball(vec 0,rho)) a b (rfa_expflow (top,atlas) g sg p E)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_FRAME_INVERTIBLE]; ALL_TAC] THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_UNION THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
  X_GEN_TAC `w0:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** w0 IN mfd_exp_dom (top,atlas) ((g:real->A->real^N^N) sg) p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tball ((g:real->A->real^N^N) sg) p rho SUBSET
                 mfd_exp_dom (top,atlas) (g sg) p` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_SIMP_TAC[CMPP_TNORM_FRAME];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `p:A`; `E:real^N^N`; `w0:real^N`]
         CMPH_EXP_FRAME_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_DEXP_INJ THEN
    EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w0) IN
    topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w0)`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                             ((E:real^N^N) ** w0))` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `Tr:real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `Tr SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `W INTER ball(vec 0:real^N,rho)` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; IN_BALL_0; INTER_SUBSET] THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET] THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC
   `\t. mpullback (\w. SND(c:(A->bool)#(A->real^N))
                         (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                                  ((E:real^N^N) ** w)))
                  (metric_local atlas c (g t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRICCI_FLOW_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`Tr:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:A topology` THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real`; `w:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_LOCAL THEN
    ASM_SIMP_TAC[]]);;

let RFA_EXPFLOW_RMD_GEN = prove
 (`!top atlas (g:real->A->real^N^N) sg (p:A) (E:real^N^N) rho j t w.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\
     riemannian_metric atlas (g sg) /\ riemannian_metric atlas (g t) /\
     p IN topspace top /\ mfd_orthonormal_frame (g sg) p E /\
     mfd_tball (g sg) p rho SUBSET mfd_exp_dom (top,atlas) (g sg) p /\
     metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) (g sg) p E) /\
     norm w < rho
     ==> lrm_deriv_norm2 j (rfa_expflow (top,atlas) g sg p E t) w =
         rfa_rmd2 j atlas (g t) (mfd_exp (top,atlas) (g sg) p (E ** w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_FRAME_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** w IN mfd_exp_dom (top,atlas) ((g:real->A->real^N^N) sg) p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tball ((g:real->A->real^N^N) sg) p rho SUBSET
                 mfd_exp_dom (top,atlas) (g sg) p` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_SIMP_TAC[CMPP_TNORM_FRAME];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) sg`; `p:A`; `E:real^N^N`; `w:real^N`]
         CMPH_EXP_FRAME_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_DEXP_INJ THEN
    EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w) IN
    topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p ((E:real^N^N) ** w)`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                             ((E:real^N^N) ** w))` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `Tr:real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `Tr SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `lrm_deriv_norm2 j
      (mpullback (\w. SND(c:(A->bool)#(A->real^N))
                        (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                                 ((E:real^N^N) ** w)))
                 (metric_local atlas c (g t))) w` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LRM_DERIV_NORM2_LOCAL THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC RFA_EXPFLOW_LOCAL THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:num`; `Tr:real^N->bool`; `W:real^N->bool`;
                 `\w. SND(c:(A->bool)#(A->real^N))
                        (mfd_exp (top,atlas) ((g:real->A->real^N^N) sg) p
                                 ((E:real^N^N) ** w))`;
                 `h':real^N->real^N`;
                 `metric_local atlas (c:(A->bool)#(A->real^N)) ((g:real->A->real^N^N) t)`;
                 `w:real^N`] LRM_DERIV_NORM2_PULLBACK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `riemannian_metric atlas ((g:real->A->real^N^N) t)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[] THEN MATCH_MP_TAC RFA_RMD2_CHART THEN
  EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[]);;

(* From the initial time: the chart extensions of ricci_flow_from pull back  *)
(* to extensions of the exp pullback flow.                                   *)

let RFA_MPULLBACK_PT = prove
 (`!(h:real^N->real^N) (G1:real^N->real^N^N) G2 z.
     G1 (h z) = G2 (h z) ==> mpullback h G1 z = mpullback h G2 z`,
  SIMP_TAC[mpullback]);;

let RFA_EXPFLOW_LFROM = prove
 (`!top atlas (g:real->A->real^N^N) a b (p:A) (E:real^N^N) rho.
     hausdorff_space top /\ ricci_flow_from (top,atlas) a b g /\
     p IN topspace top /\ mfd_orthonormal_frame (g a) p E /\
     mfd_tball (g a) p rho SUBSET mfd_exp_dom (top,atlas) (g a) p /\
     metric_field (ball(vec 0,rho)) (cmp_expmetric (top,atlas) (g a) p E)
     ==> rfa_lfrom (ball(vec 0,rho)) a b (rfa_expflow (top,atlas) g a p E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ricci_flow_from]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ricci_flow_on]) THEN
  REWRITE_TAC[rfa_lfrom; RFA_EXPFLOW_SG] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_EXPFLOW_LRICCI_GEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `w0:real^N` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `invertible(E:real^N^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RFA_FRAME_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(E:real^N^N) ** w0 IN mfd_exp_dom (top,atlas) ((g:real->A->real^N^N) a) p`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mfd_tball ((g:real->A->real^N^N) a) p rho SUBSET
                 mfd_exp_dom (top,atlas) (g a) p` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[mfd_tball; IN_ELIM_THM] THEN ASM_SIMP_TAC[CMPP_TNORM_FRAME];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) a`; `p:A`; `E:real^N^N`; `w0:real^N`]
         CMPH_EXP_FRAME_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RFA_EXPFLOW_DEXP_INJ THEN
    EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p ((E:real^N^N) ** w0) IN
    topspace top`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CMPP_EXP_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p ((E:real^N^N) ** w0)`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^N))->bool)
                    (mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p
                             ((E:real^N^N) ** w0))` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `Tr:real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `Tr SUBSET IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  USE_THEN "ext" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(c:(A->bool)#(A->real^N)) IN atlas`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN
    `Fc:real^(1,N)finite_sum->real^(N,N)finite_prod`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "feq"))))) THEN
  MAP_EVERY EXISTS_TAC
   [`W INTER ball(vec 0:real^N,rho)`; `e:real`;
    `\z. (vectorize:real^N^N->real^(N,N)finite_prod)
         (mpullback (\w. SND(c:(A->bool)#(A->real^N))
                           (mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p
                                    ((E:real^N^N) ** w)))
            ((\t y. (matrify:real^(N,N)finite_prod->real^N^N)
                    (Fc(pastecart (lift t) y))) (drop(fstcart z)))
            (sndcart z))`] THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER; IN_BALL_0; INTER_SUBSET] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift(a - e),lift b) PCROSS (W:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; INTER_SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_PULLBACK_FAMILY_SMOOTH THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RFB_ATLAS_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`;
                            `atlas:((A->bool)#(A->real^N))->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[VECTORIZE_MATRIFY; LIFT_DROP; PASTECART_FST_SND; ETA_AX] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `mpullback (\w. SND(c:(A->bool)#(A->real^N))
                     (mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p
                              ((E:real^N^N) ** w)))
              (metric_local atlas c (g t)) z` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_MPULLBACK_PT THEN BETA_TAC THEN
    SUBGOAL_THEN
     `SND(c:(A->bool)#(A->real^N))
        (mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p ((E:real^N^N) ** z)) IN
      IMAGE (SND c) (FST c)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "feq" (fun th -> SIMP_TAC[th; ASSUME `a <= t`; ASSUME `t < b`;
                                       ASSUME
     `SND(c:(A->bool)#(A->real^N))
        (mfd_exp (top,atlas) ((g:real->A->real^N^N) a) p ((E:real^N^N) ** z)) IN
      IMAGE (SND c) (FST c)`]) THEN
    REWRITE_TAC[MATRIFY_VECTORIZE];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RFA_EXPFLOW_LOCAL THEN
    ASM_SIMP_TAC[]]);;


(* ========================================================================= *)
(* The manifold step from the initial time (normal coordinates               *)
(* of g(a) at each point), all orders by induction on the regions            *)
(* [a,b) x B_a(x, r/2 + r/2^(m+1)), and P2_THM_3_29.                          *)
(* ========================================================================= *)

let RFA_MFD_SHI_STEP0 = prove
 (`!m K r1 r2 tau C A1.
     &0 < K /\ &0 < r2 /\ r2 < r1 /\ &0 < tau /\ &0 <= C /\ &0 <= A1
     ==> ?C'. !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
               (g:real->A->real^N^N) x Kc.
           hausdorff_space top /\ ricci_flow_from (top,atlas) a b g /\
           b - a <= tau /\ x IN topspace top /\ compact_in top Kc /\
           mfd_ball (top,atlas) (g a) x r1 SUBSET Kc /\
           (!t y. a <= t /\ t < b /\ y IN mfd_ball (top,atlas) (g a) x r1
                  ==> mfd_rm_norm atlas (g t) y <= K) /\
           (!j t y. j <= m /\ a <= t /\ t < b /\
                    y IN mfd_ball (top,atlas) (g a) x r1
                    ==> rfa_rmd2 j atlas (g t) y <= C) /\
           (!y. y IN mfd_ball (top,atlas) (g a) x r1
                ==> rfa_rmd2 (m + 1) atlas (g a) y <= A1)
           ==> !t y. a <= t /\ t < b /\ y IN mfd_ball (top,atlas) (g a) x r2
                     ==> rfa_rmd2 (m + 1) atlas (g t) y <= C'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho = min (inv(sqrt K)) (r1 - r2)` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= (r1 - r2) / &1 /\ K * rho pow 2 <= &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv(sqrt K) /\ &0 < r1 - r2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; SQRT_POS_LT; REAL_SUB_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < rho /\ rho <= inv(sqrt K) /\ rho <= r1 - r2`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_DIV_1] THEN
    SUBGOAL_THEN `rho pow 2 <= inv K` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(sqrt K) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ASM_SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `K * inv K` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(m:num) + 1`; `\i:num. (C:real)`; `A1:real`; `K:real`; `rho:real`;
                `tau:real`]
         (INST_TYPE [`:N`,`:N`] RFA_SLOC_STEP0)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (LABEL_TAC "loc")) THEN
  EXISTS_TAC `max C0 A1` THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "bds")
    (LABEL_TAC "init"))))))))) THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x r2 SUBSET
    mfd_ball (top,atlas) (g a) x r1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t1:real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= A1 ==> x <= max C0 A1`) THEN
    USE_THEN "init" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a < t1 /\ t1 - a <= tau` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= C0 ==> x <= max C0 A1`) THEN
  SUBGOAL_THEN
   `!s. a <= s /\ s < b
        ==> smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
            riemannian_metric atlas ((g:real->A->real^N^N) s)`
  (LABEL_TAC "rm") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `s:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
    riemannian_metric atlas ((g:real->A->real^N^N) a) /\
    riemannian_metric atlas ((g:real->A->real^N^N) t1)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "rm" (MP_TAC o SPEC `a:real`) THEN
    USE_THEN "rm" (MP_TAC o SPEC `t1:real`) THEN
    SUBGOAL_THEN `a <= a /\ a < b /\ a <= t1 /\ t1 < b` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `R = mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x r1` THEN
  SUBGOAL_THEN `open_in top (R:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:A. z IN R ==> z IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN R` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. mfd_joinable (top,atlas) (y:A) z /\
        mfd_dist (top,atlas) ((g:real->A->real^N^N) a) y z < r1 - r2 ==> z IN R`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN EXPAND_TAC "R" THEN
    UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x r2` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MFD_JOINABLE_TRANS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(g:real->A->real^N^N) a`; `x:A`; `y:A`; `z:A`] MFD_DIST_TRIANGLE) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN R ==> mfd_rm_norm atlas ((g:real->A->real^N^N) a) z <= K`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN topspace top` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) a`; `y:A`] RFA_FRAME_EXISTS) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) a`; `(g:real->A->real^N^N) a`; `R:A->bool`;
                 `Kc:A->bool`; `y:A`; `r1 - r2:real`; `&1`; `K:real`; `rho:real`;
                 `E:real^N^N`] RFA_MFD_EXPSETUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_01; REAL_POW_ONE; REAL_MUL_LID;
                 REAL_LE_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:real->A->real^N^N`; `a:real`; `b:real`; `y:A`;
                 `E:real^N^N`; `rho:real`] RFA_EXPFLOW_LFROM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!i s w. i < m + 1 /\ a <= s /\ s <= t1 /\ norm w < rho
            ==> lrm_deriv_norm2 i
                  (rfa_expflow (top,atlas) (g:real->A->real^N^N) a y E s) w <= C`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `s:real`; `w:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `riemannian_metric atlas ((g:real->A->real^N^N) s)` ASSUME_TAC THENL
     [USE_THEN "rm" (MP_TAC o SPEC `s:real`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:real->A->real^N^N`; `a:real`; `y:A`;
                   `E:real^N^N`; `rho:real`; `i:num`; `s:real`; `w:real^N`]
           RFA_EXPFLOW_RMD_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "bds" MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `mfd_exp (top,atlas) ((g:real->A->real^N^N) a) y ((E:real^N^N) ** w) IN R`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. norm w < rho
        ==> lrm_deriv_norm2 (m + 1)
              (cmp_expmetric (top,atlas) ((g:real->A->real^N^N) a) y E) w <= A1`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:real->A->real^N^N`; `a:real`; `y:A`;
                   `E:real^N^N`; `rho:real`; `(m:num) + 1`; `a:real`; `w:real^N`]
           RFA_EXPFLOW_RMD_GEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[RFA_EXPFLOW_SG] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "init" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPECL
   [`a:real`; `b:real`; `rfa_expflow (top,atlas) (g:real->A->real^N^N) a y E`;
    `t1:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RFA_EXPFLOW_SG]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:real->A->real^N^N`; `a:real`; `y:A`;
                 `E:real^N^N`; `rho:real`; `(m:num) + 1`; `t1:real`; `vec 0:real^N`]
         RFA_EXPFLOW_RMD_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_0]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `(g:real->A->real^N^N) a`; `y:A`] MFD_EXP_DOM) THEN
  ASM_SIMP_TAC[]);;

let RFA_MFD_SHI_ALL0 = prove
 (`!l K r tau. &0 < K /\ &0 < r /\ &0 < tau
     ==> !m. m <= l
             ==> ?C. &0 <= C /\
                 !(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a b
                  (g:real->A->real^N^N) x Kc.
                   hausdorff_space top /\ ricci_flow_from (top,atlas) a b g /\
                   b - a <= tau /\ x IN topspace top /\ compact_in top Kc /\
                   mfd_ball (top,atlas) (g a) x r SUBSET Kc /\
                   (!t y. a <= t /\ t < b /\ y IN mfd_ball (top,atlas) (g a) x r
                          ==> mfd_rm_norm atlas (g t) y <= K) /\
                   (!j y. j <= l /\ y IN mfd_ball (top,atlas) (g a) x r
                          ==> rfa_rmd2 j atlas (g a) y <= K)
                   ==> !j t y. j <= m /\ a <= t /\ t < b /\
                               y IN mfd_ball (top,atlas) (g a) x
                                      (r / &2 + r / &2 pow (m + 1))
                               ==> rfa_rmd2 j atlas (g t) y <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [DISCH_TAC THEN
    X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c0"))
      (INST_TYPE [`:A`,`:A`; `:N`,`:N`] RFA_R1_RMD0) THEN
    EXISTS_TAC `C0 * K pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "sec") (LABEL_TAC "init")))))))) THEN
    REWRITE_TAC[LE; real_pow; REAL_DIV_1; ADD_CLAUSES; REAL_POW_1] THEN
    SUBGOAL_THEN `r / &2 + r / &2 = r` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `t:real`; `y:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "c0" MATCH_MP_TAC THEN
    EXISTS_TAC `top:A topology` THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `a:real`; `b:real`; `g:real->A->real^N^N`; `t:real`]
           RFA_RICCI_FLOW_FROM_METRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x r` THEN
      REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
      USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(m:num) <= l` (fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cm:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
  SUBGOAL_THEN `&1 <= &2 pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_ADD; REAL_POW_1]) THEN
  REWRITE_TAC[real_pow; REAL_POW_ADD; REAL_POW_1] THEN
  ABBREV_TAC `p = &2 pow m` THEN
  SUBGOAL_THEN
   `r / ((&2 * p) * &2) = inv(&2) * (r / (p * &2)) /\
    &0 < r / (p * &2) /\ r / (p * &2) <= r / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `r / (p * &2) = (r / &2) / p` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC RFA_DIV_LE_SELF THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `K:real`; `r / &2 + r / (p * &2)`;
                `r / &2 + r / ((&2 * p) * &2)`; `tau:real`; `Cm:real`; `K:real`]
         RFA_MFD_SHI_STEP0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C':real` (LABEL_TAC "step")) THEN
  EXISTS_TAC `max Cm (max C' (&0))` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^N^N`; `x:A`; `Kc:A->bool`] THEN
  DISCH_THEN(fun th -> LABEL_TAC "hyps" th THEN
    CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "sec") (LABEL_TAC "init"))))))) th) THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `t:real`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `a:real`; `b:real`; `g:real->A->real^N^N`; `x:A`; `Kc:A->bool`]) THEN
  ANTS_TAC THENL [USE_THEN "hyps" ACCEPT_TAC; DISCH_THEN(LABEL_TAC "ihf")] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x (r / &2 + r / ((&2 * p) * &2))
    SUBSET mfd_ball (top,atlas) (g a) x (r / &2 + r / (p * &2)) /\
    mfd_ball (top,atlas) (g a) x (r / &2 + r / (p * &2)) SUBSET
    mfd_ball (top,atlas) (g a) x r`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RFA_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `(j:num) <= m` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= Cm ==> x <= max Cm (max C' (&0))`) THEN
    USE_THEN "ihf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:num) = m + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= C' ==> x <= max Cm (max C' (&0))`) THEN
  SUBGOAL_THEN `mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x (r / &2 + r / (p * &2))
                SUBSET Kc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t y. a <= t /\ t < b /\
          y IN mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x (r / &2 + r / (p * &2))
          ==> mfd_rm_norm atlas (g t) y <= K`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `z:A`] THEN STRIP_TAC THEN
    USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN mfd_ball (top,atlas) ((g:real->A->real^N^N) a) x (r / &2 + r / (p * &2))
        ==> rfa_rmd2 (m + 1) atlas (g a) y <= K`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    USE_THEN "init" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "step" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
    `a:real`; `b:real`; `g:real->A->real^N^N`; `x:A`; `Kc:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "stepf")] THEN
  USE_THEN "stepf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* P2_THM_3_29 (MT Thm 3.29, ball at the initial time, bounds on the        *)
(* initial derivatives): the dimension-3 instance of RFA_MFD_SHI_ALL0 at    *)
(* m = l on B_a(x, r/2), with the compact closure of B_a(x,r).              *)

let RFA_P2_THM_3_29 = prove
 (`!u:A->bool. P2_THM_3_29_STATEMENT u`,
  REWRITE_TAC[P2_THM_3_29_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:num`; `K:real`; `r:real`; `tau:real`]
    (INST_TYPE [`:A`,`:A`; `:3`,`:N`] RFA_MFD_SHI_ALL0)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
  REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "all"))) THEN
  EXISTS_TAC `C:real` THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                       `a:real`; `b:real`; `g:real->A->real^3^3`; `x:A`] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`j:num`; `t:real`; `y:A`] THEN STRIP_TAC THEN
  USE_THEN "all" (MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
    `g:real->A->real^3^3`; `x:A`;
    `top closure_of mfd_ball (top,atlas) ((g:real->A->real^3^3) a) x r`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[rfa_rmd2] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    REWRITE_TAC[SUBSET; mfd_ball; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE) THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`j:num`; `t:real`; `y:A`]) THEN
  REWRITE_TAC[rfa_rmd2] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:A) IN mfd_ball (top,atlas) ((g:real->A->real^3^3) a) x (r / &2)` THEN
  REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r / &2` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_DIV THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_POW_LE; REAL_POS]);;

