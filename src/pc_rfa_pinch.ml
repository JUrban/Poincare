(* ========================================================================= *)
(* Unit pc_rfa_pinch: the Hamilton-Ivey pinching estimate along a 3D Ricci   *)
(* flow on a closed manifold (Morgan-Tian Theorem 4.32, the statement        *)
(* P2_THM_4_32_STATEMENT of pc_p3_iface, proved as RFA_P2_THM_4_32): the     *)
(* weak maximum principle (RFA_MINP_BARRIER) for the pinching function       *)
(*   (1+t) R/2 - h(max 1 ((1+t) X)), X = -lambda, h(y) = y (log y - 3),      *)
(* with the Rayleigh barrier for lambda.                                     *)
(* ========================================================================= *)

needs "src/pc_rfa_smaxv.ml";;
needs "src/pc_rfa_secpres.ml";;

prioritize_real();;
type_invention_error := true;;


(* ========================================================================= *)
(* The scalar function h(y) = y (log y - 3), the ODE inequality              *)
(* of Hamilton-Ivey (Morgan-Tian Claim 4.31, (4.3)-(4.4)) and the reaction   *)
(* bound at a bad point (RFA_HI_REACTION).                                  *)
(* ========================================================================= *)

(* The function h(y) = y (log y - 3) of the Hamilton-Ivey pinching (MT     *)
(* f_t(x) = x (log x + log(1+t) - 3) = h(x(1+t)) / (1+t)).                  *)

let rfa_hiv = new_definition
 `rfa_hiv (y:real) = y * (log y - &3)`;;

let RFA_HIV_1 = prove
 (`rfa_hiv(&1) = --(&3)`,
  REWRITE_TAC[rfa_hiv; LOG_1] THEN REAL_ARITH_TAC);;

let RFA_HIV_DERIV = prove
 (`!y. &0 < y ==> (rfa_hiv has_real_derivative (log y - &2)) (atreal y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfa_hiv = (\y. y * (log y - &3))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfa_hiv]; ALL_TAC] THEN
  SUBGOAL_THEN `log y - &2 = y * (inv y - &0) + &1 * (log y - &3)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_MUL_ATREAL THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ID] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG; HAS_REAL_DERIVATIVE_CONST]);;

let RFA_HIV_LE_NEG3Y = prove
 (`!y. &0 < y /\ y <= &1 ==> rfa_hiv y <= --(&3) * y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hiv] THEN
  SUBGOAL_THEN `log y <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&1)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
                    REWRITE_TAC[LOG_1; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `y * log y <= &0` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= y * --l ==> y * l <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* h is decreasing on [1, e^2] (so h <= -3 there) and increasing on       *)
(* [e^2, infinity).                                                         *)

let RFA_HIV_LE_NEG3 = prove
 (`!y. &1 <= y /\ y <= exp(&2) ==> rfa_hiv y <= --(&3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y. --(rfa_hiv y)`; `\y. --(log y - &2)`;
                 `real_interval[&1,exp(&2)]`; `&1`; `y:real`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL; RFA_HIV_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN
      MATCH_MP_TAC RFA_HIV_DERIV THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `log x <= &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&2))` THEN
        CONJ_TAC THENL [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
                        REWRITE_TAC[LOG_EXP; REAL_LE_REFL]];
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let RFA_HIV_MONO = prove
 (`!y1 y2. exp(&2) <= y1 /\ y1 <= y2 ==> rfa_hiv y1 <= rfa_hiv y2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rfa_hiv`; `\y. log y - &2`;
                 `{y | exp(&2) <= y}`; `y1:real`; `y2:real`]
         HAS_REAL_DERIVATIVE_INCREASING_IMP) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC RFA_HIV_DERIV THEN
    MP_TAC(SPEC `&2` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&2 <= l ==> &0 <= l - &2`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&2))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ASM_REAL_ARITH_TAC]);;

(* The inverse-free reformulation used below: h(y) = y log y - 3y gives      *)
(* h'(y) = (s - F)/y + 1 where F = s - h(y).                                 *)

let RFA_HIV_DERIV_FORM = prove
 (`!y s. &0 < y ==> log y - &2 = (s - (s - rfa_hiv y)) / y + &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hiv; REAL_ARITH `s - (s - h) = h`] THEN
  UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD);;

(* MT Claim 4.31 in the sectional normalization: with X = -p1, Y = -p2,    *)
(* l = p3 (p1 <= p2 <= p3), I = X Y^2 + l Y (Y - X) + l^2 (X - Y) >= 0.      *)

let RFA_HI_CLAIM431 = prove
 (`!p1 p2 p3. p1 <= p2 /\ p2 <= p3 /\ p1 < &0
              ==> &0 <= --p1 * p2 pow 2 + p3 * --p2 * (--p2 - --p1) +
                         p3 pow 2 * (--p1 - --p2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= p2` THENL
   [SUBGOAL_THEN `&0 <= --p1 * p2 pow 2 /\ &0 <= p3 * --p2 * (--p2 - --p1) /\
                  &0 <= p3 pow 2 * (--p1 - --p2)` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `--p2 * (--p2 - --p1) = p2 * (p2 - p1)` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    SUBGOAL_THEN
     `--p1 * p2 pow 2 + p3 * --p2 * (--p2 - --p1) + p3 pow 2 * (--p1 - --p2) =
      (--p2) pow 3 + (--p1 - --p2) * ((p3 - --p2 / &2) pow 2 + &3 / &4 * p2 pow 2)`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC]]);;

(* MT (4.3)-(4.4) with the factor 2 of the sectional normalization:        *)
(* X S' - (X + S) X' >= 2 X^3, S' = |Ric|^2, X' = -2 (p1^2 + p2 p3).        *)

let RFA_HI_ODE44_ORD = prove
 (`!p1 p2 p3. p1 <= p2 /\ p2 <= p3 /\ p1 < &0
              ==> &2 * (--p1) pow 3 <=
                  --p1 * ((p2 + p3) pow 2 + (p1 + p3) pow 2 + (p1 + p2) pow 2) -
                  (--p1 + (p1 + p2 + p3)) * (--(&2) * (p1 pow 2 + p2 * p3))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p1:real`; `p2:real`; `p3:real`] RFA_HI_CLAIM431) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let RFA_HI_ODE44 = prove
 (`!p1 p2 p3. p1 <= p2 /\ p1 <= p3 /\ p1 < &0
              ==> &2 * (--p1) pow 3 <=
                  --p1 * ((p2 + p3) pow 2 + (p1 + p3) pow 2 + (p1 + p2) pow 2) -
                  (--p1 + (p1 + p2 + p3)) * (--(&2) * (p1 pow 2 + p2 * p3))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p2 <= p3` THENL
   [MATCH_MP_TAC RFA_HI_ODE44_ORD THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`p1:real`; `p3:real`; `p2:real`] RFA_HI_ODE44_ORD) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]]);;

(* The robust boundary condition of the Hamilton-Ivey pinching: with        *)
(* X = -p1, y = (1+t) X > e^2, F = (1+t) S - h(y) < 0, the ODE derivative of *)
(* F (the reaction the barrier sees) is >= L F, L = 2 K/m + 1.               *)

let RFA_HI_XP_BOUND = prove
 (`!X Xp K m. &0 < m /\ m <= X /\ Xp <= &2 * K /\ &0 <= K
              ==> Xp / X <= &2 * K / m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&2 * K / m) * X = (&2 * K) * (X / m)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let RFA_HI_REACTION = prove
 (`!p1 p2 p3 t K m.
     p1 <= p2 /\ p1 <= p3 /\ &0 <= t /\ abs(p2 * p3) <= K /\ &0 < m /\ m <= --p1 /\
     exp(&2) < (&1 + t) * --p1 /\
     (&1 + t) * (p1 + p2 + p3) - rfa_hiv((&1 + t) * --p1) < &0
     ==> (&2 * K / m + &1) *
         ((&1 + t) * (p1 + p2 + p3) - rfa_hiv((&1 + t) * --p1)) <=
         (&1 + t) * ((p2 + p3) pow 2 + (p1 + p3) pow 2 + (p1 + p2) pow 2) +
         (p1 + p2 + p3) +
         (log((&1 + t) * --p1) - &2) * (p1 + (&1 + t) * &2 * (p1 pow 2 + p2 * p3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `X = --p1` THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p1 < &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p1:real`; `p2:real`; `p3:real`] RFA_HI_ODE44) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `y = (&1 + t) * X` THEN
  SUBGOAL_THEN `&1 <= y /\ &0 < y` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&2` REAL_EXP_POS_LT) THEN
    SUBGOAL_THEN `&1 <= exp(&2)` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = p1 + p2 + p3` THEN
  ABBREV_TAC `Sp = (p2 + p3) pow 2 + (p1 + p3) pow 2 + (p1 + p2) pow 2` THEN
  ABBREV_TAC `Xp = --(&2) * (p1 pow 2 + p2 * p3)` THEN
  ABBREV_TAC `H = rfa_hiv y` THEN
  SUBGOAL_THEN `log y = H / y + &3` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[rfa_hiv] THEN
    UNDISCH_TAC `&0 < y` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `FF = (&1 + t) * S - H` THEN
  SUBGOAL_THEN
   `(&1 + t) * Sp + S + ((H / y + &3) - &2) * (p1 + (&1 + t) * &2 * (p1 pow 2 + p2 * p3)) =
    (&1 + t) / X * (X * Sp - (X + S) * Xp) - X + FF / y * (X + (&1 + t) * Xp)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["FF"; "Xp"; "y"; "X"] THEN
    SUBGOAL_THEN `~(--p1 = &0) /\ ~(&1 + t = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X + (&1 + t) * Xp) / y <= &2 * K / m + &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(X + (&1 + t) * Xp) / y = inv(&1 + t) + Xp / X` SUBST1_TAC THENL
     [EXPAND_TAC "y" THEN SUBGOAL_THEN `~(X = &0) /\ ~(&1 + t = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&1 + t) <= &1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Xp / X <= &2 * K / m` MP_TAC THENL
     [MATCH_MP_TAC RFA_HI_XP_BOUND THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
        EXPAND_TAC "Xp" THEN MP_TAC(SPEC `p1:real` REAL_LE_POW_2) THEN
        UNDISCH_TAC `abs(p2 * p3) <= K` THEN REAL_ARITH_TAC;
        MP_TAC(SPEC `p2 * p3:real` REAL_ABS_POS) THEN
        UNDISCH_TAC `abs(p2 * p3) <= K` THEN REAL_ARITH_TAC];
      UNDISCH_TAC `inv(&1 + t) <= &1` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FF < &0` ASSUME_TAC THENL
   [EXPAND_TAC "FF" THEN EXPAND_TAC "H" THEN EXPAND_TAC "y" THEN
    EXPAND_TAC "X" THEN EXPAND_TAC "S" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * K / m + &1) * FF <= FF / y * (X + (&1 + t) * Xp)` ASSUME_TAC THENL
   [SUBGOAL_THEN `FF / y * (X + (&1 + t) * Xp) = FF * ((X + (&1 + t) * Xp) / y)`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --FF * (L - Q) ==> L * FF <= FF * Q`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + t) / X * (X * Sp - (X + S) * Xp) - X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + t) / X * (&2 * X pow 3) - X` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(&1 + t) / X * (&2 * X pow 3) - X = X * (&2 * y - &1)` SUBST1_TAC THENL
       [EXPAND_TAC "y" THEN UNDISCH_TAC `&0 < X` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - X <= b - X`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* R and |Ric|^2 in an eigenframe, and the Rayleigh barrier for              *)
(* lambda with the frame values (RFA_SECMIN_BARRIER_HI).                     *)
(* ========================================================================= *)

(* In an orthonormal Ricci eigenframe (3D): R = 2 (p1 + p2 + p3) and        *)
(* |Ric|^2 = (p2 + p3)^2 + (p1 + p3)^2 + (p1 + p2)^2, p_i = P(f_i,f_i).     *)

let RFA_P3_FRAME_SCALARS = prove
 (`!U (G:real^3->real^3^3) y (S:real^3^3).
     metric_field U G /\ y IN U /\ invertible S /\ matrix_inv(G y) = transp S ** S /\
     (!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci G y (transp S ** basis i) (transp S ** basis j) = &0)
     ==> lscalar G y = &2 * (lpcurv G y (\m. transp S ** basis 1) +
                             lpcurv G y (\m. transp S ** basis 2) +
                             lpcurv G y (\m. transp S ** basis 3)) /\
         ltnorm2 2 G (lric2 G) y =
           (lpcurv G y (\m. transp S ** basis 2) +
            lpcurv G y (\m. transp S ** basis 3)) pow 2 +
           (lpcurv G y (\m. transp S ** basis 1) +
            lpcurv G y (\m. transp S ** basis 3)) pow 2 +
           (lpcurv G y (\m. transp S ** basis 1) +
            lpcurv G y (\m. transp S ** basis 2)) pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field U (G:real^3->real^3^3)`) (ASSUME `(y:real^3) IN U`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= 3
        ==> lpcurv (G:real^3->real^3^3) y (\m. transp(S:real^3^3) ** basis i) =
            lscalar G y / &2 - lricci G y (transp(S:real^3^3) ** basis i) (transp(S:real^3^3) ** basis i)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[lpcurv; lmetric2; lric2] THEN
    MP_TAC(ISPECL [`(G:real^3->real^3^3) y`; `S:real^3^3`; `i:num`; `i:num`]
           RFA_GFRAME_ORTHO) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lscalar (G:real^3->real^3^3) y =
    lricci G y (transp(S:real^3^3) ** basis 1) (transp(S:real^3^3) ** basis 1) +
    lricci G y (transp(S:real^3^3) ** basis 2) (transp(S:real^3^3) ** basis 2) +
    lricci G y (transp(S:real^3^3) ** basis 3) (transp(S:real^3^3) ** basis 3)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_SCAL_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ltnorm2 2 (G:real^3->real^3^3) (lric2 G) y =
    lricci G y (transp(S:real^3^3) ** basis 1) (transp(S:real^3^3) ** basis 1) pow 2 +
    lricci G y (transp(S:real^3^3) ** basis 2) (transp(S:real^3^3) ** basis 2) pow 2 +
    lricci G y (transp(S:real^3^3) ** basis 3) (transp(S:real^3^3) ** basis 3) pow 2`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y:real^3`; `S:real^3^3`]
           RFA_RICNORM_FRAME) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; SUM_3] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC
     `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3 /\ ~(i = j)
            ==> lricci (G:real^3->real^3^3) y (transp(S:real^3^3) ** basis i)
                       (transp(S:real^3^3) ** basis j) = &0` THEN
    DISCH_THEN(fun th ->
      MAP_EVERY (fun (i,j) -> MP_TAC(SPECL [mk_small_numeral i; mk_small_numeral j] th))
        [1,2; 1,3; 2,1; 2,3; 3,1; 3,2]) THEN
    REWRITE_TAC[ARITH] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MAP_EVERY (fun i -> MP_TAC(SPEC (mk_small_numeral i) th)) [1; 2; 3]) THEN
  REWRITE_TAC[ARITH] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING);;

(* The Rayleigh barrier for lambda at a chart_at point, with the frame     *)
(* values: R = 2 (lambda + p2 + p3), |Ric|^2 in the eigenvalues, |p2|, |p3| *)
(* bounded by sqrt |Rm|^2, and the Laplacian identity at every point.      *)

let RFA_SECMIN_BARRIER_HI = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) U t0 x0.
     ricci_flow_on (top,atlas) a b g /\ open_in top U /\ a < t0 /\ t0 < b /\ x0 IN U
     ==> ?d W (phi:real->real^3->real) D p2 p3.
           &0 < d /\ open W /\ SND(chart_at atlas x0) x0 IN W /\
           W SUBSET IMAGE (SND(chart_at atlas x0)) (FST(chart_at atlas x0) INTER U) /\
           (!y. y IN W
                ==> mfd_sec_min atlas (g t0) (chart_inv (chart_at atlas x0) y) <=
                    phi t0 y) /\
           phi t0 (SND(chart_at atlas x0) x0) = mfd_sec_min atlas (g t0) x0 /\
           (!t. t0 - d < t /\ t <= t0
                ==> mfd_sec_min atlas (g t) x0 <= phi t (SND(chart_at atlas x0) x0)) /\
           smooth_map_on W (\y. lift(phi t0 y)) /\
           ((\t. phi t (SND(chart_at atlas x0) x0)) has_real_derivative D)
             (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
           mfd_sec_min atlas (g t0) x0 <= p2 /\ mfd_sec_min atlas (g t0) x0 <= p3 /\
           abs p2 <= sqrt(rfa_rmd2 0 atlas (g t0) x0) /\
           abs p3 <= sqrt(rfa_rmd2 0 atlas (g t0) x0) /\
           mfd_scalar atlas (g t0) x0 = &2 * (mfd_sec_min atlas (g t0) x0 + p2 + p3) /\
           ltnorm2 2 (metric_local atlas (chart_at atlas x0) (g t0))
                     (lric2 (metric_local atlas (chart_at atlas x0) (g t0)))
                     (SND(chart_at atlas x0) x0) =
           (p2 + p3) pow 2 + (mfd_sec_min atlas (g t0) x0 + p3) pow 2 +
           (mfd_sec_min atlas (g t0) x0 + p2) pow 2 /\
           llap (metric_local atlas (chart_at atlas x0) (g t0)) (phi t0)
                (SND(chart_at atlas x0) x0) +
           &2 * (mfd_sec_min atlas (g t0) x0 pow 2 + p2 * p3) = D`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_scalar] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:A) IN topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`;
                 `U:A->bool`] RFA_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^3)) x0` THEN
  ABBREV_TAC `V = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`; `b:real`;
                 `g:real->A->real^3^3`; `c:(A->bool)#(A->real^3)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) /\
    (y0:real^3) IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ASSUME `lricci_flow V a b
        (\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))`) THEN
      REWRITE_TAC[lricci_flow] THEN
      DISCH_THEN(MP_TAC o SPEC `t0:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["y0"; "V"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(g:real->A->real^3^3) t0`; `c:(A->bool)#(A->real^3)`; `x0:A`]
         RFA_SECMIN_CHART_3D) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^3->bool`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                 `y0:real^3`; `S:real^3^3`] RFA_P3_MIN_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`;
                 `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                 `y0:real^3`; `S:real^3^3`] RFA_P3_FRAME_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `f1 = transp(S:real^3^3) ** basis 1` THEN
  ABBREV_TAC `f2 = transp(S:real^3^3) ** basis 2` THEN
  ABBREV_TAC `f3 = transp(S:real^3^3) ** basis 3` THEN
  SUBGOAL_THEN
   `f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y0 - y0) f1 = f1` ASSUME_TAC THENL
   [MATCH_MP_TAC RFA_EXT_AT THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f1:real^3 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f1) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)
        ==> y IN V /\ chart_inv c y IN FST c /\ SND c (chart_inv c y) = y`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN V` ASSUME_TAC THENL
     [EXPAND_TAC "V" THEN UNDISCH_TAC
       `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)` THEN
      SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                  ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)} =
      IMAGE (SND c) (FST c INTER U) INTER
      {y | (\y. f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1) y IN (:real^3) DIFF {vec 0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DIFF; OPEN_UNIV; CLOSED_SING] THEN X_GEN_TAC `z:real^3` THEN
    MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `\h. --(christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 h f1)` THEN
    MATCH_MP_TAC RFA_EXT_HAS_DERIVATIVE THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN {y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "y0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)} SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(MATCH_MP LRG_METRIC_INVERTIBLE
    (CONJ (ASSUME `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))`) (ASSUME `(y0:real^3) IN V`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= 3 /\ 1 <= j /\ j <= 3
          ==> (transp(S:real^3^3) ** basis i) dot
              (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** (transp S ** basis j)) = if i = j then &1 else &0`
  (LABEL_TAC "orth") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RFA_GFRAME_ORTHO THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `f2 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &1 /\ f3 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &1 /\
    f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &0 /\ f1 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &0 /\
    f2 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f3) = &0 /\ f3 dot (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0 ** f2) = &0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "orth" (fun th ->
      MAP_EVERY (fun (i,j) -> MP_TAC(SPECL [mk_small_numeral i; mk_small_numeral j] th))
        [2,2; 3,3; 1,2; 1,3; 2,3; 3,2]) THEN
    REWRITE_TAC[ARITH; ASSUME `transp(S:real^3^3) ** basis 1 = f1`;
                ASSUME `transp(S:real^3^3) ** basis 2 = f2`;
                ASSUME `transp(S:real^3^3) ** basis 3 = f3`] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t0 - a:real` THEN
  EXISTS_TAC
   `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}` THEN
  EXISTS_TAC
   `\t y. lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)) y
            (\m. f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1) /
          ((f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1) dot
           (metric_local atlas c (g t) y **
            (f1 - christoffel (metric_local atlas c (g t0)) y0 (y - y0) f1)))` THEN
  EXISTS_TAC
   `ltlap 2 (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) (lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))) y0 (\m. f1) +
    &2 * (lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1) pow 2 +
          lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f2) * lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f3))` THEN
  EXISTS_TAC `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f2)` THEN
  EXISTS_TAC `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f3)` THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* d > 0 *)
    ASM_REAL_ARITH_TAC;
    (* W SUBSET IMAGE *)
    SET_TAC[];
    (* spatial barrier *)
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U)`)) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `c:(A->bool)#(A->real^3)`;
                   `chart_inv (c:(A->bool)#(A->real^3)) y`;
                   `f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1`] RFA_SECMIN_RAYLEIGH) THEN
    ASM_SIMP_TAC[];
    (* value at y0 *)
    REWRITE_TAC[REAL_DIV_1];
    (* time barrier *)
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `c:(A->bool)#(A->real^3)`; `x0:A`;
                   `f1:real^3`] RFA_SECMIN_RAYLEIGH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]];
    (* smoothness *)
    MATCH_MP_TAC RFA_RQ_EXT_SMOOTH THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_ELIM_THM];
    (* derivative *)
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MP_TAC(BETA_RULE(ISPECL [`V:real^3->bool`; `a:real`; `b:real`;
       `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
       `t0:real`; `y0:real^3`; `S:real^3^3`] RFA_BARRIER_REACTION)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    (* p2 bound *)
    MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`;
                   `f1:real^3`; `f3:real^3`; `f2:real^3`] RFA_LSECTIONAL_PCURV_3D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`] LRG_METRIC_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `x0:A`; `f1:real^3`; `f3:real^3`]
           RFA_MFD_SECTIONAL_LE_RMD2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_ORTHO_NONCOLLINEAR THEN
      EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    (* p3 bound *)
    MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`;
                   `f1:real^3`; `f2:real^3`; `f3:real^3`] RFA_LSECTIONAL_PCURV_3D) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`V:real^3->bool`; `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`; `y0:real^3`] LRG_METRIC_SYM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`; `x0:A`; `f1:real^3`; `f2:real^3`]
           RFA_MFD_SECTIONAL_LE_RMD2) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC RFA_ORTHO_NONCOLLINEAR THEN
      EXISTS_TAC `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0) y0` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[mfd_sectional] THEN REAL_ARITH_TAC;
    (* llap *)
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x + z = y + z:real`) THEN
    MATCH_MP_TAC RFA_BARRIER_LAP2 THEN
    MAP_EVERY EXISTS_TAC
     [`V:real^3->bool`; `{y:real^3 | y IN IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER U) /\
                     ~(f1 - christoffel (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (y - y0) f1 = vec 0)}`; `lpcurv (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0 (\m. f1)`] THEN
    ASM_REWRITE_TAC[lmetric2] THEN SIMP_TAC[IN_ELIM_THM]]);;

(* ========================================================================= *)
(* The pinching function rfa_hipf, its relation to                           *)
(* rfs_pinched_at, R >= 6 lambda, preservation of (i), continuity.          *)
(* ========================================================================= *)

(* The pinching function of Hamilton-Ivey at time t (MT Theorem 4.32):      *)
(* (1+t) R/2 - h(max 1 ((1+t) X)), X = -lambda.  Condition (ii) of the      *)
(* pinching is equivalent to its nonnegativity when R >= 6 lambda.          *)

let rfa_hipf = new_definition
 `rfa_hipf (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (t:real) (x:A) =
    (&1 + t) * mfd_scalar atlas g x / &2 -
    rfa_hiv(max (&1) ((&1 + t) * --(mfd_sec_min atlas g x)))`;;

let RFA_HI_PINCH_EQUIV = prove
 (`!t R lam. &0 <= t /\ &6 * lam <= R
     ==> ((&0 < --lam ==> &2 * --lam * (log(--lam) + log(&1 + t) - &3) <= R) <=>
          &0 <= (&1 + t) * R / &2 - rfa_hiv(max (&1) ((&1 + t) * --lam)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 + t) * R / &2 + &3 * (&1 + t) * --lam` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + t) * R / &2 + &3 * (&1 + t) * --lam =
                  (&1 + t) * (R / &2 - &3 * lam)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < --lam` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `(&1 + t) * --lam <= &0` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_MUL_RNEG; REAL_NEG_LE0] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> max (&1) x = &1`; RFA_HIV_1] THEN
    ASM_REAL_ARITH_TAC] THEN
  ABBREV_TAC `X = --lam` THEN
  SUBGOAL_THEN `&0 < &1 + t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + t) * X` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * X * (log X + log(&1 + t) - &3) <= R) <=>
    (rfa_hiv((&1 + t) * X) <= (&1 + t) * R / &2)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `rfa_hiv((&1 + t) * X) = ((&1 + t) / &2) * (&2 * X * (log X + log(&1 + t) - &3)) /\
      (&1 + t) * R / &2 = ((&1 + t) / &2) * R`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[rfa_hiv] THEN
      MP_TAC(SPECL [`&1 + t`; `X:real`] LOG_MUL) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_LE_LMUL_EQ THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= (&1 + t) * X` THENL
   [ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> max (&1) x = x`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(&1 <= x) ==> max (&1) x = &1`; RFA_HIV_1] THEN
  MP_TAC(SPEC `(&1 + t) * X` RFA_HIV_LE_NEG3Y) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* R >= 6 lambda in dimension 3 (R = 2 (p1 + p2 + p3), p1 = lambda minimal). *)

let RFA_SCALAR_GE_6SECMIN = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ x IN topspace top
     ==> &6 * mfd_sec_min atlas g x <= mfd_scalar atlas g x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x:A`]
         CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `g:A->real^3^3`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)`;
                 `x:A`] RFA_SECMIN_CHART_3D) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)))
                        (FST(chart_at atlas x)))
                 (metric_local atlas (chart_at atlas x) (g:A->real^3^3)) /\
    SND(chart_at atlas x) x IN IMAGE (SND(chart_at atlas x)) (FST(chart_at atlas x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `riemannian_metric (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3)` THEN
      REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A))) (FST(chart_at atlas x))`;
    `metric_local atlas (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) (g:A->real^3^3)`;
    `SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x:A)) x`; `S:real^3^3`]
   RFA_P3_FRAME_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[mfd_scalar] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* rfs_pinched_at at time t >= 0 is (i) together with rfa_hipf >= 0.       *)

let RFA_HI_PINCHED_IFF = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) t x.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     x IN topspace top /\ &0 <= t
     ==> (rfs_pinched_at atlas g t x <=>
          --(&6) / (&4 * t + &1) <= mfd_scalar atlas g x /\
          &0 <= rfa_hipf atlas g t x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pinched_at; rfa_hipf] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC RFA_HI_PINCH_EQUIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RFA_SCALAR_GE_6SECMIN THEN EXISTS_TAC `top:A topology` THEN
  ASM_REWRITE_TAC[]);;

(* Condition (i) of the pinching, R >= -6/(4t+1), is preserved (scalar     *)
(* maximum principle, RFA_SCALAR_LOWER from time a with r0 = -6/(4a+1)).   *)

let RFA_HI_SCALAR_BOUND = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3).
     compact_space top /\ ricci_flow_from (top,atlas) a b g /\ &0 <= a /\
     (!x. x IN topspace top ==> --(&6) / (&4 * a + &1) <= mfd_scalar atlas (g a) x)
     ==> !t x. a <= t /\ t < b /\ x IN topspace top
               ==> --(&6) / (&4 * t + &1) <= mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `a:real`; `--(&6) / (&4 * a + &1)`]
         RFA_SCALAR_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real`; `x:A`]) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&3 * --(&6) / (&4 * a + &1) / (&3 - &2 * (t - a) * --(&6) / (&4 * a + &1)) =
    --(&6) / (&4 * t + &1)`
  (fun th -> ASM_MESON_TAC[th]) THEN
  SUBGOAL_THEN `~(&4 * a + &1 = &0) /\ ~(&4 * t + &1 = &0) /\
                ~(&3 - &2 * (t - a) * --(&6) / (&4 * a + &1) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

(* Continuity of the pinching function on [a,b) x M.                      *)

let RFA_HIV_MAX1_CONTINUOUS = prove
 (`(\u. rfa_hiv(max (&1) u)) real_continuous_on (:real)`,
  SIMP_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN
  SUBGOAL_THEN `(\u. rfa_hiv(max (&1) u)) = rfa_hiv o (\u. max (&1) u)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_MAX THEN
    REWRITE_TAC[REAL_CONTINUOUS_CONST; REAL_CONTINUOUS_AT_ID];
    REWRITE_TAC[] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_ATREAL THEN
    EXISTS_TAC `log(max (&1) x) - &2` THEN MATCH_MP_TAC RFA_HIV_DERIV THEN
    REAL_ARITH_TAC]);;

let RFA_HIPF_CONTINUOUS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3).
     ricci_flow_from (top,atlas) a b g
     ==> continuous_map
           (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                          (subtopology top (topspace top)),
            euclideanreal)
           (\z. rfa_hipf atlas (g (FST z)) (FST z) (SND z))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  SUBGOAL_THEN
   `continuous_map
      (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                     (subtopology (top:A topology) (topspace top)),
       euclideanreal) (FST:real#A->real)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclideanreal {t | a <= t /\ t < b}`;
                   `subtopology (top:A topology) (topspace top)`] CONTINUOUS_MAP_FST) THEN
    SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
      (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                     (subtopology (top:A topology) (topspace top)),
       euclideanreal)
      (\z. mfd_scalar (atlas:((A->bool)#(A->real^3))->bool)
                      ((g:real->A->real^3^3) (FST z)) (SND z)) /\
    continuous_map
      (prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                     (subtopology (top:A topology) (topspace top)),
       euclideanreal)
      (\z. mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                       ((g:real->A->real^3^3) (FST z)) (SND z))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RFA_MFD_SCALAR_CONTINUOUS_GEN;
      MATCH_MP_TAC RFA_SECMIN_CONTINUOUS_GEN] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ricci_flow_from];
    ALL_TAC] THEN
  REWRITE_TAC[rfa_hipf] THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_RMUL THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST];
    ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`prod_topology (subtopology euclideanreal {t | a <= t /\ t < b})
                   (subtopology (top:A topology) (topspace top))`;
    `\z:real#A. (&1 + FST z) *
                --(mfd_sec_min (atlas:((A->bool)#(A->real^3))->bool)
                               ((g:real->A->real^3^3) (FST z)) (SND z))`;
    `\u. rfa_hiv(max (&1) u)`] TOPC_CONTINUOUS_MAP_REAL_COMPOSE)) THEN
  REWRITE_TAC[RFA_HIV_MAX1_CONTINUOUS] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST];
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_NEG THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* The barrier of the pinching function at a bad point                       *)
(* (RFA_HI_BARRIER).                                                         *)
(* ========================================================================= *)

(* A bad point of the pinching function at time t >= 0 with condition (i)  *)
(* has y = (1+t) X > e^2: there (1+t) R/2 >= -3 and h <= -3 on [1,e^2].     *)

let RFA_HI_BAD_POINT = prove
 (`!t R y. &0 <= t /\ --(&6) / (&4 * t + &1) <= R /\
           (&1 + t) * R / &2 - rfa_hiv(max (&1) y) < &0
           ==> exp(&2) < y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(&3) <= (&1 + t) * R / &2` ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 <= R` THENL
     [SUBGOAL_THEN `&0 <= (&1 + t) * R` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t * --R` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `--(&6) <= R * (&4 * t + &1)` MP_TAC THENL
     [UNDISCH_TAC `--(&6) / (&4 * t + &1) <= R` THEN
      SUBGOAL_THEN `&0 < &4 * t + &1` (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th]) THEN
      ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 <= t * --R` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPEC `max (&1) y` RFA_HIV_LE_NEG3) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Smoothness and the Laplacian of h(u) for u > 0.                         *)

let RFA_SMOOTH_HIV_COMPOSE = prove
 (`!s (u:real^N->real).
     open s /\ smooth_map_on s (\y. lift(u y)) /\ (!y. y IN s ==> &0 < u y)
     ==> smooth_map_on s (\y. lift(rfa_hiv(u y)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfa_hiv] THEN
  MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift((u:real^N->real) y)`]
         SMOOTH_MAP_ON_LIFT_LOG) THEN
  ASM_SIMP_TAC[LIFT_DROP]);;

let RFA_LLAP_HIV_COMPOSE = prove
 (`!s (G:real^N->real^N^N) u y.
     open s /\ smooth_map_on s (\z. lift(u z)) /\ (!z. z IN s ==> &0 < u z) /\ y IN s
     ==> llap G (\z. rfa_hiv(u z)) y =
         (log(u y) - &2) * llap G u y + inv(u y) * lgrad2 G u y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `{x:real | &0 < x}`; `G:real^N->real^N^N`;
                 `u:real^N->real`; `rfa_hiv`; `\x:real. log x - &2`;
                 `\x:real. inv x`; `y:real^N`] RFA_LLAP_COMPOSE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[IN_ELIM_THM; RFA_HIV_DERIV] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `inv x = inv x - &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
  ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_LOG; HAS_REAL_DERIVATIVE_CONST]);;

(* The barrier inequality at a bad point, in the shape produced by the      *)
(* derivative and Laplacian rules for the pinching barrier.                 *)

let RFA_HI_BARRIER_ALG = prove
 (`!t lam p2 p3 K m LR Lq Dq lg R N2.
     lam <= p2 /\ lam <= p3 /\ &0 <= t /\ abs(p2 * p3) <= K /\ &0 < m /\ m <= --lam /\
     exp(&2) < (&1 + t) * --lam /\
     (&1 + t) * R / &2 - rfa_hiv((&1 + t) * --lam) < &0 /\
     R = &2 * (lam + p2 + p3) /\
     N2 = (p2 + p3) pow 2 + (lam + p3) pow 2 + (lam + p2) pow 2 /\
     Lq + &2 * (lam pow 2 + p2 * p3) = Dq /\ &0 <= lg
     ==> ((&1 + t) * (inv(&2) * LR) -
          ((log((&1 + t) * --lam) - &2) * ((&1 + t) * --Lq) +
           inv((&1 + t) * --lam) * lg)) +
         (&2 * K / m + &1) * ((&1 + t) * R / &2 - rfa_hiv((&1 + t) * --lam))
         <= ((&1 + t) * (inv(&2) * (LR + &2 * N2)) + (&0 + &1) * (R / &2)) -
            (log((&1 + t) * --lam) - &2) * ((&1 + t) * --Dq + (&0 + &1) * --lam)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`lam:real`; `p2:real`; `p3:real`; `t:real`; `K:real`; `m:real`]
         RFA_HI_REACTION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(&1 + t) * R / &2 - rfa_hiv((&1 + t) * --lam) < &0` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv((&1 + t) * --lam) * lg` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MP_TAC(SPEC `&2` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `Lq + &2 * (lam pow 2 + p2 * p3) = Dq` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `lY = log((&1 + t) * --lam) - &2` THEN
  ABBREV_TAC `hY = rfa_hiv((&1 + t) * --lam)` THEN
  ABBREV_TAC `ig = inv((&1 + t) * --lam) * lg` THEN
  ABBREV_TAC `L = &2 * K / m + &1` THEN
  REAL_ARITH_TAC);;

(* The barrier of the pinching function at a bad point (t0,x0): with       *)
(* q the Rayleigh barrier of lambda, phi = (1+t) R/2 - h((1+t) (-q)) lies    *)
(* above the pinching function near (t0,x0) and satisfies                   *)
(* llap phi + L F <= dphi/dt there, L = 2 C^2/m + 1.                         *)

let RFA_HI_BARRIER = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3) t0 x0 C m.
     ricci_flow_on (top,atlas) a b g /\ &0 <= a /\ a < t0 /\ t0 < b /\
     x0 IN topspace top /\
     --(&6) / (&4 * t0 + &1) <= mfd_scalar atlas (g t0) x0 /\
     rfa_hipf atlas (g t0) t0 x0 < &0 /\
     sqrt(rfa_rmd2 0 atlas (g t0) x0) <= C /\ &0 < m /\ (&1 + t0) * m <= exp(&2)
     ==> ?d W (phi:real->real^3->real) D.
           &0 < d /\ open W /\ SND(chart_at atlas x0) x0 IN W /\
           W SUBSET IMAGE (SND(chart_at atlas x0))
                          (FST(chart_at atlas x0) INTER topspace top) /\
           (!y. y IN W
                ==> rfa_hipf atlas (g t0) t0 (chart_inv (chart_at atlas x0) y) <=
                    phi t0 y) /\
           phi t0 (SND(chart_at atlas x0) x0) = rfa_hipf atlas (g t0) t0 x0 /\
           (!t. t0 - d < t /\ t <= t0
                ==> rfa_hipf atlas (g t) t x0 <= phi t (SND(chart_at atlas x0) x0)) /\
           smooth_map_on W (\y. lift(phi t0 y)) /\
           ((\t. phi t (SND(chart_at atlas x0) x0)) has_real_derivative D)
             (atreal t0 within {s | t0 - d <= s /\ s <= t0}) /\
           llap (metric_local atlas (chart_at atlas x0) (g t0)) (phi t0)
                (SND(chart_at atlas x0) x0) +
           (&2 * C pow 2 / m + &1) * rfa_hipf atlas (g t0) t0 x0 <= D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:A topology)
                  (atlas:((A->bool)#(A->real^3))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a < t /\ t < b ==> riemannian_metric atlas ((g:real->A->real^3^3) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `topspace(top:A topology)`;
                 `t0:real`; `x0:A`] RFA_SECMIN_BARRIER_HI) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `W1:real^3->bool`
    (X_CHOOSE_THEN `q:real->real^3->real` (X_CHOOSE_THEN `Dq:real`
     (X_CHOOSE_THEN `p2:real` (X_CHOOSE_THEN `p3:real` STRIP_ASSUME_TAC)))))) THEN
  (* the bad point *)
  SUBGOAL_THEN
   `exp(&2) < (&1 + t0) * --(mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0)`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`t0:real`; `mfd_scalar atlas ((g:real->A->real^3^3) t0) x0`;
                  `(&1 + t0) * --(mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0)`]
           RFA_HI_BAD_POINT) THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `rfa_hipf atlas ((g:real->A->real^3^3) t0) t0 x0 < &0` THEN
      REWRITE_TAC[rfa_hipf]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= exp(&2)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the chart *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `x0:A`;
                 `topspace(top:A topology)`] RFA_CHART_AT_FACTS) THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`]
         LRG_RICCI_FLOW_ON_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!y. y IN W1
        ==> mfd_scalar atlas ((g:real->A->real^3^3) t0)
                       (chart_inv (chart_at atlas x0) y) =
            lscalar (metric_local atlas (chart_at atlas x0) (g t0)) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(y:real^3) IN IMAGE (SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)))
                          (FST(chart_at atlas x0))`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[mfd_scalar] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t0`;
                   `chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)`;
                   `chart_inv (chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)) y`]
           RFA_MFD_SCALAR_CHART) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (x0:A)` THEN
  ABBREV_TAC `y0 = SND (c:(A->bool)#(A->real^3)) x0` THEN
  ABBREV_TAC `V = IMAGE (SND (c:(A->bool)#(A->real^3))) (FST c)` THEN
  SUBGOAL_THEN
   `!t. mfd_scalar atlas ((g:real->A->real^3^3) t) x0 =
        lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t)) y0`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[mfd_scalar] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `lam0 = mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0` THEN
  SUBGOAL_THEN
   `metric_field V (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) /\
    (y0:real^3) IN V`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ASSUME `lricci_flow V a b
        (\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t))`) THEN
      REWRITE_TAC[lricci_flow] THEN
      DISCH_THEN(MP_TAC o SPEC `t0:real` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY EXPAND_TAC ["y0"; "V"] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W1:real^3->bool) SUBSET V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN UNDISCH_TAC
     `(W1:real^3->bool) SUBSET IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c INTER topspace top)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + t0 /\ &0 < exp(&2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m <= --lam0` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    SUBGOAL_THEN `(&1 + t0) * m < (&1 + t0) * --lam0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
    ALL_TAC] THEN
  (* smoothness in space *)
  SUBGOAL_THEN
   `smooth_map_on W1 (\y. lift((&1 + t0) * --((q:real->real^3->real) t0 y)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. lift((&1 + t0) * --((q:real->real^3->real) t0 y))) =
      (\y. --(&1 + t0) % lift(q t0 y))`
    SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = {y:real^3 | y IN W1 /\ exp(&2) < (&1 + t0) * --((q:real->real^3->real) t0 y)}` THEN
  SUBGOAL_THEN `open (W:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN
    SUBGOAL_THEN
     `{y:real^3 | y IN W1 /\ exp(&2) < (&1 + t0) * --((q:real->real^3->real) t0 y)} =
      {y | y IN W1 /\ (\y. lift((&1 + t0) * --(q t0 y))) y IN {x:real^1 | x$1 > exp(&2)}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM drop; LIFT_DROP; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN W ==> y IN W1 /\ exp(&2) < (&1 + t0) * --((q:real->real^3->real) t0 y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET W1 /\ W SUBSET V` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN CONJ_TAC THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN W ==> &0 < (&1 + t0) * --((q:real->real^3->real) t0 y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_TRANS THEN
    EXISTS_TAC `exp(&2)` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on W (\y. lift((q:real->real^3->real) t0 y)) /\
    smooth_map_on W (\y. lift((&1 + t0) * --((q:real->real^3->real) t0 y))) /\
    smooth_map_on W (\y. lift(--((q:real->real^3->real) t0 y))) /\
    smooth_map_on W (\y. lift(lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                        ((g:real->A->real^3^3) t0)) y)) /\
    smooth_map_on W (\y. lift(lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                        ((g:real->A->real^3^3) t0)) y / &2)) /\
    smooth_map_on W (\y. lift((&1 + t0) *
                              lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                        ((g:real->A->real^3^3) t0)) y / &2)) /\
    smooth_map_on W (\y. lift(rfa_hiv((&1 + t0) * --((q:real->real^3->real) t0 y))))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `smooth_map_on W (\y. lift((q:real->real^3->real) t0 y)) /\
      smooth_map_on W (\y. lift((&1 + t0) * --((q:real->real^3->real) t0 y))) /\
      smooth_map_on W (\y. lift(lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                          ((g:real->A->real^3^3) t0)) y)) /\
      smooth_map_on W (\y. lift(lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                          ((g:real->A->real^3^3) t0)) y / &2))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THENL
       [EXISTS_TAC `W1:real^3->bool`; EXISTS_TAC `W1:real^3->bool`;
        EXISTS_TAC `V:real^3->bool`; EXISTS_TAC `V:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LRG_LSCALAR_SMOOTH; MATCH_MP_TAC RFA_HALF_SCALAR_SMOOTH] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_NEG] THEN MATCH_MP_TAC SMOOTH_MAP_ON_NEG_OPEN THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LRG_SMOOTH_LIFT_MUL_REAL THEN ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      MATCH_MP_TAC RFA_SMOOTH_HIV_COMPOSE THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* time derivatives *)
  SUBGOAL_THEN
   `((\t. (&1 + t) * --((q:real->real^3->real) t y0)) has_real_derivative
     ((&1 + t0) * --Dq + (&0 + &1) * --(q t0 y0)))
    (atreal t0 within {s | t0 - d1 <= s /\ s <= t0})`
  (LABEL_TAC "T1") THENL
   [MP_TAC(ISPECL [`\t:real. &1 + t`; `&0 + &1`;
                   `\t. --((q:real->real^3->real) t y0)`; `--Dq:real`; `t0:real`;
                   `{s | t0 - d1 <= s /\ s <= t0}`] HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID];
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_NEG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d2. &0 < d2 /\
         !t. t0 - d2 < t /\ t <= t0
             ==> exp(&2) < (&1 + t) * --((q:real->real^3->real) t y0)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "T1" (MP_TAC o MATCH_MP HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL) THEN
    REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `(&1 + t0) * --lam0 - exp(&2)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min dd d1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t:real = t0` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. (&1 + t) * lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3) t)) y0 / &2 -
          rfa_hiv((&1 + t) * --((q:real->real^3->real) t y0))) has_real_derivative
     (((&1 + t0) *
       (inv(&2) *
        (llap (metric_local atlas c (g t0)) (lscalar (metric_local atlas c (g t0))) y0 +
         &2 * ltnorm2 2 (metric_local atlas c (g t0))
                        (lric2 (metric_local atlas c (g t0))) y0)) +
       (&0 + &1) * (lscalar (metric_local atlas c (g t0)) y0 / &2)) -
      (log((&1 + t0) * --(q t0 y0)) - &2) *
      ((&1 + t0) * --Dq + (&0 + &1) * --(q t0 y0))))
    (atreal t0 within {s | t0 - d1 <= s /\ s <= t0})`
  (LABEL_TAC "T3") THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\t:real. &1 + t`; `&0 + &1`;
                     `\t. lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                     ((g:real->A->real^3^3) t)) y0 / &2`;
                     `inv(&2) *
                      (llap (metric_local atlas (c:(A->bool)#(A->real^3))
                                          ((g:real->A->real^3^3) t0))
                            (lscalar (metric_local atlas c (g t0))) y0 +
                       &2 * ltnorm2 2 (metric_local atlas c (g t0))
                                      (lric2 (metric_local atlas c (g t0))) y0)`;
                     `t0:real`; `{s | t0 - d1 <= s /\ s <= t0}`]
             HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
        REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; HAS_REAL_DERIVATIVE_ID];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(\t. lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                        ((g:real->A->real^3^3) t)) y0 / &2) =
        (\t. inv(&2) * lscalar (metric_local atlas c (g t)) y0)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_LMUL_WITHIN THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(BETA_RULE(ISPECL [`V:real^3->bool`; `a:real`; `b:real`;
         `\t. metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t)`;
         `t0:real`; `y0:real^3`] LSCALAR_EVOLUTION)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\t. rfa_hiv((&1 + t) * --((q:real->real^3->real) t y0))) =
      rfa_hiv o (\t. (&1 + t) * --(q t y0))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. (&1 + t) * --((q:real->real^3->real) t y0)`; `rfa_hiv`;
                   `(&1 + t0) * --Dq + (&0 + &1) * --((q:real->real^3->real) t0 y0)`;
                   `log((&1 + t0) * --((q:real->real^3->real) t0 y0)) - &2`;
                   `t0:real`; `{s | t0 - d1 <= s /\ s <= t0}`] REAL_DIFF_CHAIN_WITHIN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [USE_THEN "T1" ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    MATCH_MP_TAC RFA_HIV_DERIV THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the Laplacian of the barrier at y0 *)
  SUBGOAL_THEN
   `llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
         (\y. (&1 + t0) * lscalar (metric_local atlas c (g t0)) y / &2 -
              rfa_hiv((&1 + t0) * --((q:real->real^3->real) t0 y))) y0 =
    (&1 + t0) * (inv(&2) * llap (metric_local atlas c (g t0))
                                (lscalar (metric_local atlas c (g t0))) y0) -
    ((log((&1 + t0) * --(q t0 y0)) - &2) *
     ((&1 + t0) * --(llap (metric_local atlas c (g t0)) (q t0) y0)) +
     inv((&1 + t0) * --(q t0 y0)) *
     lgrad2 (metric_local atlas c (g t0)) (\y. (&1 + t0) * --(q t0 y)) y0)`
  (LABEL_TAC "T4") THENL
   [MP_TAC(ISPECL [`W:real^3->bool`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                   `\y. (&1 + t0) * lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                                ((g:real->A->real^3^3) t0)) y / &2`;
                   `\y. rfa_hiv((&1 + t0) * --((q:real->real^3->real) t0 y))`;
                   `y0:real^3`] RFA_LLAP_SUB) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THENL
     [MP_TAC(ISPECL [`W:real^3->bool`;
                     `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                     `\y. lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                     ((g:real->A->real^3^3) t0)) y / &2`;
                     `&1 + t0`; `y0:real^3`] RFA_LLAP_CMUL) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN
       `(\y. lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                        ((g:real->A->real^3^3) t0)) y / &2) =
        (\y. inv(&2) * lscalar (metric_local atlas c (g t0)) y)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`W:real^3->bool`;
                     `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                     `lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                 ((g:real->A->real^3^3) t0))`;
                     `inv(&2)`; `y0:real^3`] RFA_LLAP_CMUL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                   `\y. (&1 + t0) * --((q:real->real^3->real) t0 y)`; `y0:real^3`]
           RFA_LLAP_HIV_COMPOSE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                   `\y. --((q:real->real^3->real) t0 y)`; `&1 + t0`; `y0:real^3`]
           RFA_LLAP_CMUL) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`W:real^3->bool`;
                   `metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)`;
                   `(q:real->real^3->real) t0`; `y0:real^3`] RFA_LLAP_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
    ALL_TAC] THEN
  (* the pinching function at (t0,x0) and the barrier inequalities *)
  SUBGOAL_THEN
   `rfa_hipf atlas ((g:real->A->real^3^3) t0) t0 x0 =
    (&1 + t0) * lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t0)) y0 / &2 -
    rfa_hiv((&1 + t0) * --lam0)`
  (LABEL_TAC "H0") THENL
   [REWRITE_TAC[rfa_hipf;
      ASSUME `!t. mfd_scalar atlas ((g:real->A->real^3^3) t) x0 =
                  lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t)) y0`;
      ASSUME `mfd_sec_min atlas ((g:real->A->real^3^3) t0) x0 = lam0`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> max (&1) x = x`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN W
        ==> rfa_hipf atlas ((g:real->A->real^3^3) t0) t0
                     (chart_inv (c:(A->bool)#(A->real^3)) y) <=
            (&1 + t0) * lscalar (metric_local atlas c (g t0)) y / &2 -
            rfa_hiv((&1 + t0) * --((q:real->real^3->real) t0 y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(y:real^3) IN W1 /\ exp(&2) < (&1 + t0) * --((q:real->real^3->real) t0 y)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfa_hipf] THEN
    SUBGOAL_THEN
     `mfd_scalar atlas ((g:real->A->real^3^3) t0) (chart_inv (c:(A->bool)#(A->real^3)) y) =
      lscalar (metric_local atlas c (g t0)) y`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `h2 <= h1 ==> a - h1 <= a - h2:real`) THEN
    SUBGOAL_THEN
     `(&1 + t0) * --((q:real->real^3->real) t0 y) <=
      (&1 + t0) * --(mfd_sec_min atlas ((g:real->A->real^3^3) t0)
                                 (chart_inv (c:(A->bool)#(A->real^3)) y))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> --b <= --a:real`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `max (&1) ((&1 + t0) * --(mfd_sec_min atlas ((g:real->A->real^3^3) t0)
                                            (chart_inv (c:(A->bool)#(A->real^3)) y))) =
      (&1 + t0) * --(mfd_sec_min atlas (g t0) (chart_inv c y))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> max (&1) x = x`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_HIV_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t0 - min d1 (min d2 (t0 - a)) < t /\ t <= t0
        ==> rfa_hipf atlas ((g:real->A->real^3^3) t) t x0 <=
            (&1 + t) * lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t)) y0 / &2 -
            rfa_hiv((&1 + t) * --((q:real->real^3->real) t y0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t0 - d1 < t /\ t0 - d2 < t /\ a < t` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[rfa_hipf;
      ASSUME `!t. mfd_scalar atlas ((g:real->A->real^3^3) t) x0 =
                  lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t)) y0`] THEN
    MATCH_MP_TAC(REAL_ARITH `h2 <= h1 ==> a - h1 <= a - h2:real`) THEN
    SUBGOAL_THEN `exp(&2) < (&1 + t) * --((q:real->real^3->real) t y0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 + t) * --((q:real->real^3->real) t y0) <=
      (&1 + t) * --(mfd_sec_min atlas ((g:real->A->real^3^3) t) x0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> --b <= --a:real`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `max (&1) ((&1 + t) * --(mfd_sec_min atlas ((g:real->A->real^3^3) t) x0)) =
      (&1 + t) * --(mfd_sec_min atlas (g t) x0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> max (&1) x = x`) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC RFA_HIV_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* assembling the barrier *)
  EXISTS_TAC `min d1 (min d2 (t0 - a))` THEN EXISTS_TAC `W:real^3->bool` THEN
  EXISTS_TAC
   `\t y. (&1 + t) * lscalar (metric_local atlas (c:(A->bool)#(A->real^3))
                                ((g:real->A->real^3^3) t)) y / &2 -
          rfa_hiv((&1 + t) * --((q:real->real^3->real) t y))` THEN
  EXISTS_TAC
   `((&1 + t0) *
     (inv(&2) *
      (llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
            (lscalar (metric_local atlas c (g t0))) y0 +
       &2 * ltnorm2 2 (metric_local atlas c (g t0))
                      (lric2 (metric_local atlas c (g t0))) y0)) +
     (&0 + &1) * (lscalar (metric_local atlas c (g t0)) y0 / &2)) -
    (log((&1 + t0) * --((q:real->real^3->real) t0 y0)) - &2) *
    ((&1 + t0) * --Dq + (&0 + &1) * --(q t0 y0))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `W1:real^3->bool` THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "H0" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ASSUME `(q:real->real^3->real) t0 y0 = lam0`];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `{s | t0 - d1 <= s /\ s <= t0}` THEN CONJ_TAC THENL
     [USE_THEN "T3" ACCEPT_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "T4" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "H0" (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ASSUME `(q:real->real^3->real) t0 y0 = lam0`] THEN
  MP_TAC(SPECL
   [`t0:real`; `lam0:real`; `p2:real`; `p3:real`; `C pow 2`; `m:real`;
    `llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
          (lscalar (metric_local atlas c (g t0))) y0`;
    `llap (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
          ((q:real->real^3->real) t0) y0`;
    `Dq:real`;
    `lgrad2 (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
            (\y. (&1 + t0) * --((q:real->real^3->real) t0 y)) y0`;
    `lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0)) y0`;
    `ltnorm2 2 (metric_local atlas (c:(A->bool)#(A->real^3)) ((g:real->A->real^3^3) t0))
              (lric2 (metric_local atlas c (g t0))) y0`]
   RFA_HI_BARRIER_ALG) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_MUL; REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "H0" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(SPEC `t0:real` (ASSUME
      `!t. mfd_scalar atlas ((g:real->A->real^3^3) t) x0 =
           lscalar (metric_local atlas (c:(A->bool)#(A->real^3)) (g t)) y0`)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC LGRAD2_POS THEN EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[]]);;


(* ========================================================================= *)
(* Preservation of the pinching (RFA_HI_PINCH_PRESERVED) and                 *)
(* the headline RFA_P2_THM_4_32.                                           *)
(* ========================================================================= *)

(* The Hamilton-Ivey pinching estimate (MT Theorem 4.32): pinching at the   *)
(* initial time a >= 0 is preserved along a 3D Ricci flow on a closed       *)
(* manifold.  (i) by the scalar maximum principle; (ii) as rfa_hipf >= 0 by  *)
(* the weak maximum principle with the barrier RFA_HI_BARRIER on [a,c),     *)
(* c < b, with L = 2 C^2/m + 1, C a bound of |Rm| and m = e^2/(1+c).        *)

let RFA_HI_PINCH_PRESERVED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) a b (g:real->A->real^3^3).
     compact_space top /\ &0 <= a /\ ricci_flow_from (top,atlas) a b g /\
     (!x. x IN topspace top ==> rfs_pinched_at atlas (g a) a x)
     ==> !t x. a <= t /\ t < b /\ x IN topspace top
               ==> rfs_pinched_at atlas (g t) t x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RFA_FLOW_FROM_METRICS) THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b /\ x IN topspace top
          ==> --(&6) / (&4 * t + &1) <=
              mfd_scalar (atlas:((A->bool)#(A->real^3))->bool) ((g:real->A->real^3^3) t) x`
  (LABEL_TAC "sc") THENL
   [MATCH_MP_TAC RFA_HI_SCALAR_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[rfs_pinched_at];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. a <= t /\ t < b /\ x IN topspace top
          ==> &0 <= rfa_hipf (atlas:((A->bool)#(A->real^3))->bool)
                             ((g:real->A->real^3^3) t) t x`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) t`; `t:real`; `x:A`] RFA_HI_PINCHED_IFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]] THEN
  MAP_EVERY X_GEN_TAC [`t1:real`; `x1:A`] THEN STRIP_TAC THEN
  ABBREV_TAC `c = (t1 + b) / &2` THEN
  SUBGOAL_THEN `t1 < c /\ c < b` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                 `b:real`; `g:real->A->real^3^3`; `topspace(top:A topology)`; `c:real`]
         RFA_RMD2_SQRT_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM compact_space] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = exp(&2) / (&1 + c)` THEN
  SUBGOAL_THEN `&0 < m /\ !t. a <= t /\ t <= c ==> (&1 + t) * m <= exp(&2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "m" THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN EXPAND_TAC "m" THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(x * y) * z = y * (x * z):real`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topspace(top:A topology)`; `a:real`; `c:real`; `g:real->A->real^3^3`;
                 `\t x. rfa_hipf (atlas:((A->bool)#(A->real^3))->bool)
                                 ((g:real->A->real^3^3) t) t (x:A)`;
                 `\t:real u:real. (&2 * C pow 2 / m + &1) * u`; `\t:real. &0`]
         RFA_MINP_BARRIER) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [(* atlas *)
    FIRST_ASSUM ACCEPT_TAC;
    (* compact *)
    ASM_REWRITE_TAC[GSYM compact_space];
    (* open *)
    REWRITE_TAC[OPEN_IN_TOPSPACE];
    (* a < c *)
    ASM_REAL_ARITH_TAC;
    (* metrics *)
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    (* continuity *)
    MATCH_MP_TAC RFA_CMAP_RESTRICT_TU THEN EXISTS_TAC `b:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; SUBSET_REFL] THEN
    MATCH_MP_TAC RFA_HIPF_CONTINUOUS THEN ASM_REWRITE_TAC[];
    (* Lipschitz *)
    REPEAT STRIP_TAC THEN EXISTS_TAC `abs(&2 * C pow 2 / m + &1)` THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL; REAL_LE_REFL];
    (* H' = psi(t,H) *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST];
    (* initial *)
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(g:real->A->real^3^3) a`; `a:real`; `x:A`] RFA_HI_PINCHED_IFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(fun th -> MP_TAC(EQ_MP th (MATCH_MP (ASSUME
      `!x. x IN topspace top ==> rfs_pinched_at (atlas:((A->bool)#(A->real^3))->bool)
                                                ((g:real->A->real^3^3) a) a x`)
      (ASSUME `(x:A) IN topspace top`)))) THEN
    SIMP_TAC[];
    (* the barrier *)
    MAP_EVERY X_GEN_TAC [`t0:real`; `x0:A`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `a:real`;
                   `b:real`; `g:real->A->real^3^3`; `t0:real`; `x0:A`; `C:real`; `m:real`]
           RFA_HI_BARRIER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `W:real^3->bool`
      (X_CHOOSE_THEN `phi:real->real^3->real` (X_CHOOSE_THEN `D:real`
        STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `W:real^3->bool`; `phi:real->real^3->real`; `D:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* The statement P2_THM_4_32_STATEMENT (pc_p3_iface): Hamilton-Ivey         *)
(* pinching is preserved along a Ricci flow on a closed 3-manifold.         *)

let RFA_P2_THM_4_32 = prove
 (`!u:A->bool. P2_THM_4_32_STATEMENT u`,
  REWRITE_TAC[P2_THM_4_32_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_HI_PINCH_PRESERVED THEN ASM_REWRITE_TAC[]);;

